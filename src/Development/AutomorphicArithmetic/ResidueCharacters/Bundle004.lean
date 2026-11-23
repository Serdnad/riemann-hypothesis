module

public import Development.AutomorphicArithmetic.ResidueCharacters.ExistsUnion
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle432
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseFont
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle004
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle008
public import Development.AutomorphicArithmetic.ResidueCharacters.RowDef
public import Development.AutomorphicArithmetic.ResidueCharacters.InvariantsKilledOverCyclotomicAlt
public import Development.AutomorphicArithmetic.ResidueCharacters.NumBounds
public import Development.AutomorphicArithmetic.ResidueCharacters.Bundle002
public import Development.AutomorphicArithmetic.ResidueCharacters.NumCost
import Development.AutomorphicArithmetic.ResidueCharacters.NumParameters
public import Development.AutomorphicArithmetic.ResidueCharacters.NumSplit
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
open Module GlobalTheory.LiftExpSplit

namespace UpperTheory.N

variable {D : D7}

theorem liftAt_of_liftK (i : D.nd.Loc) (N : ℕ) (hK : LiftK (D.loc (D.nd.l i))) (hC : CycAt N i)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    {ι : Type} {k : ℕ} (Ms : ι → Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥C.LL.1)
    (hc : ∀ x v, Continuous fun g => (Ms x g).mulVec v)
    (hF : TruncatedSeriesCountingIdentities.FontaineAt (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 ↥(OL C.LL)) (h : ℕ)
    (hcr : ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Ms x)))
    (hS : ∀ x τ, JumpsInV (Br.PD D.loc D.nbr i w hw) (matRep (Ms x)) τ (Set.Icc (-(h : ℤ)) h)) :
    LiftAt (Br.PD D.loc D.nbr i w hw) (O := ↥(OL C.LL)) (fun x : ι => ⇑(Ms x)) (eL (D.nd.l i) N h) := by
  intro V1 _ _ _ _ _ _ _ _ _ _ _ ρ1 L1 hc1 hs1 V2 _ _ _ _ _ _ _ _ _ _ _ ρ2 L2 hc2 hs2 F hF'
  let T₁ : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
    { V := V1, ρ := ρ1, cont := hc1, L := L1 }
  let T₂ : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
    { V := V2, ρ := ρ2, cont := hc2, L := L2 }
  obtain ⟨hcr1, hj1⟩ := subquot_crys (PD := Br.PD D.loc D.nbr i w hw) Ms hc hF
    (S := fun _ => Set.Icc (-(h : ℤ)) h) hcr hS T₁ hs1
  obtain ⟨hcr2, -⟩ := subquot_crys (PD := Br.PD D.loc D.nbr i w hw) Ms hc hF
    (S := fun _ => Set.Icc (-(h : ℤ)) h) hcr hS T₂ hs2
  exact hK N h (D.nbr i w hw).Kw C.LL (hC w hw C) T₁ T₂ F hcr1 hcr2 hF' hj1

theorem lift_exponent_admissible_cols_rows_of_crystalline (L : SizeData₂ D) (i : D.nd.Loc) (N : ℕ) (hK : LiftK (D.loc (D.nd.l i))) (hC : CycAt N i)
    (X : KillingConditions.HubData D) (dc : TruncatedSeriesCountingIdentities.Decl D i) (hgood : ∀ i, GoodR D.nd i (X.r i)) (ep : Bool) (hA : AdmissibleParameterJ.hodgeTateJumpsAtModulesForSign D ep)
    (he : AdmissibleParameterJ.JumpAbsoluteBound L) (hFont : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i)
    (hT : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) x,
      IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x))))
    (hD : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) x,
      IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i (X.r i) x)))) :
    EmbeddingTypes.LiftExponentColumn i (X.r i) dc (eL (D.nd.l i) N (Formalism.MainNotions.N.hN L)) ∧
      EmbeddingTypes.LiftExponentDualPlaces i (X.r i) dc (eL (D.nd.l i) N (Formalism.MainNotions.N.hN L)) := by
  have hcont : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i (X.r i) := continuous_family_of D i (X.r i) (hgood i)
  have hj := D.nd.j_range i
  have hhB : AdmissibleParameterJ.hJ L + 2 = Formalism.MainNotions.TwistedPlaces.hB L := by
    unfold AdmissibleParameterJ.hJ Formalism.MainNotions.TwistedPlaces.hB; ring

  have hwinT : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i) τ,
      JumpsInV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x))) τ
        (Set.Icc (-(Formalism.MainNotions.N.hN L : ℤ)) (Formalism.MainNotions.N.hN L)) := by
    intro w hw C x τ a ha
    obtain ⟨g, ρ, -, hx, -⟩ := hA i (X.r i) (hgood i) w hw C τ
    have hq := (hx x a).1.mp ha
    have hb := he.1 (D.nd.j i) hj.1 hj.2 ρ _ _ hq
    have hb2 := he.2.1
    apply mem_window L a
    have hc : (((a : ℚ) : ℝ)) = (a : ℝ) := by push_cast; rfl
    rw [hc] at hb
    linarith
  have hwinD : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i) τ,
      JumpsInV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i (X.r i) x))) τ
        (Set.Icc (-(Formalism.MainNotions.N.hN L : ℤ)) (Formalism.MainNotions.N.hN L)) := by
    intro w hw C x τ a ha
    obtain ⟨g, ρ, -, hx, -⟩ := hA i (X.r i) (hgood i) w hw C τ
    have hq := (hx x a).2.2.1.mp ha
    have hb := he.1 (D.nd.j i) hj.1 hj.2 ρ _ _ hq
    have hb2 := he.2.1
    apply mem_window L a
    have hc : (((-(a : ℚ) - 1 : ℚ)) : ℝ) = -(a : ℝ) - 1 := by push_cast; rfl
    rw [hc] at hb
    rw [abs_le] at hb ⊢
    constructor <;> linarith [hb.1, hb.2]
  refine ⟨?_, ?_⟩
  · intro w hw _ C _
    exact liftAt_of_liftK i N hK hC w hw C (fun x => TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x))
      (fun x v => locC_cont D i _ (rTwO_cont D i (X.r i) hcont x) w hw C v) (hFont w hw C)
      (Formalism.MainNotions.N.hN L) (hT w hw C) (fun x => hwinT w hw C x)
  · intro w hw _ C _
    exact liftAt_of_liftK i N hK hC w hw C (fun x => TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i (X.r i) x))
      (fun x v => locC_cont D i _ (rDuO_cont i (X.r i) hcont x) w hw C v) (hFont w hw C)
      (Formalism.MainNotions.N.hN L) (hD w hw C) (fun x => hwinD w hw C x)

end UpperTheory.N

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace UpperTheory.N

def RowOnAt {D : D7} (L : SizeData₂ D) (ρ : FamilyRepresentationConstants.RhoFam D) (Q : ℕ → Prop) (A B : ℝ) : Prop :=
  ∀ k, TwistedPlaces.TwLoc D k → Q (D.nd.l k) → ∀ π ∈ D.nd.Zgood k, Bd ρ k π (costC L A B (D.nd.l k))

end UpperTheory.N

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace UpperTheory.N

variable {D : D7}

theorem lam_eq (L : SizeData₂ D) (l : ℕ) : RowSmall.abelian₂ L l = Num.lam l (sN l D.host.condN) (RowSmall.hB L) := rfl

theorem sl_eq (D : D7) (l : ℕ) : RowSmall.sl D l = sN l D.host.condN := rfl

theorem one_le_hB (L : SizeData₂ D) (P : ParameterChoice' D L) : 1 ≤ RowSmall.hB L :=
  (Num.one_le_b L).trans (Num.hB_bounds L P).1

theorem condN_le_hB (L : SizeData₂ D) (P : ParameterChoice' D L) : (D.host.condN : ℝ) ≤ RowSmall.hB L :=
  (Num.condN_le L P).trans (Num.hB_bounds L P).1

theorem t_le_hB (L : SizeData₂ D) (P : ParameterChoice' D L) : (D.R.t : ℝ) ≤ RowSmall.hB L :=
  (Num.sizes_le_b L P).2.2.trans (Num.hB_bounds L P).1

theorem localLevel_eq_smallPrimeLevel (i : D.nd.Loc) (hs : D.nd.l i ∈ D.host.small) : D.nd.s0 i = RowSmall.sl D (D.nd.l i) := by
  by_cases h2 : D.nd.l i = 2
  · have h1 : 1 ≤ D.host.QS.factorization (D.nd.l i) := by
      have h := Nat.mem_primeFactors.1 hs
      exact h.1.factorization_pos_of_dvd h.2.2 h.2.1
    unfold RowSmall.sl
    rw [Num.factorization_condN D hs, max_eq_right h1, D.nd.restNLevelExponent_of_two i h2, h2]
  · exact Num.s0_eq i hs h2

theorem bound_smallPrime_of_splitBound (L : SizeData₂ D) (P : ParameterChoice' D L) (ρ : FamilyRepresentationConstants.RhoFam D) (hK : KillingConditions.KillAt ρ) (hSha : TwistedPlaces.ShaFinOdd D)
    (i : D.nd.Loc) (hTw : TwistedPlaces.TwLoc D i) (hs : D.nd.s0 i = RowSmall.sl D (D.nd.l i)) (π : D.nd.X i)
    (hπ : π ∈ D.nd.Zgood i) (dc : TruncatedSeriesCountingIdentities.Decl D i) (e' : ℕ) (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ) {c : ℝ}
    (hc : 1 ≤ c) (he : (e' : ℝ) ≤ c * RowSmall.hB L * (RowSmall.sl D (D.nd.l i) : ℝ))
    (hc0 : ∀ u ∈ dc.col, (c0 u : ℝ) ≤ c * D.R.f * D.R.nV * RowSmall.abelian₂ L (D.nd.l i))
    (hW : ∀ u ∈ dc.col, (Br.h0W i u (ρ i) π : ℝ) ≤ c * D.R.r * D.R.f * D.R.nV * RowSmall.abelian₂ L (D.nd.l i))
    (hB : (cB : ℝ) ≤ c * D.R.t * D.R.f * D.R.nV * RowSmall.abelian₂ L (D.nd.l i))
    (hh : (h0 D.nd i dc.col : ℝ) ≤ c * RowSmall.abelian₂ L (D.nd.l i))
    (hz : ∀ v ∈ D.nd.Q i, D.nd.zeta i v ≠ 1) (hconds : EmbeddingTypes.ShaBoundTheoremB i (ρ i) π dc e' c0 cB) :
    Bd ρ i π (costC L (6 * c) (30 * c) (D.nd.l i)) := by
  have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
  obtain ⟨hK1, hK2⟩ := hK i hTw
  obtain ⟨hFin, -⟩ := hK1 π hπ
  have hShaT : ∀ e ∈ Finset.Ioo 0 D.R.t, GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤ := by
    intro e he
    rw [Finset.mem_Ioo] at he
    exact lt_top_iff_ne_top.2 (@hSha (D.nd.l i) (D.nd.lPrime i) e he.1 he.2)
  have hIco : Finset.Ico 1 D.R.t = Finset.Ioo 0 D.R.t := by
    ext e; simp only [Finset.mem_Ico, Finset.mem_Ioo]; omega
  have hVV : TwistedPlaces.VVr D (D.nd.l i) = ((∑ e ∈ Finset.Ioo 0 D.R.t, D.what₂.shaLen (D.nd.l i) e : ℚ) : ℝ) := by
    unfold TwistedPlaces.VVr
    simp only [Rows.Data.VV, hIco]
  have hT := (Rat.cast_le (K := ℝ)).2 (hconds hFin hShaT hz)
  have hs0 : (D.nd.s0 i : ℝ) + 1 ≤ RowSmall.abelian₂ L (D.nd.l i) := by
    rw [hs]
    exact Num.s_le_lam hl.two_le (one_le_hB L P)
  have hb := Num.boundSplit_le i (ρ i) π dc e' c0 cB (y := RowSmall.hB L * (RowSmall.sl D (D.nd.l i) : ℝ)) hc hs0
    (by rw [← mul_assoc]; exact he) hc0 hW hB hh
  unfold Bd costC TwistedPlaces.vhE
  rw [hVV]
  have e : 6 * c * D.R.f * D.R.m * (RowSmall.hB L * (RowSmall.sl D (D.nd.l i) : ℝ)) =
      6 * c * D.R.f * D.R.m * RowSmall.hB L * (RowSmall.sl D (D.nd.l i) : ℝ) := by ring
  linarith

theorem bound_smallPrime_of_splitBound_cyclotomic_of_level_eq (L : SizeData₂ D) (P : ParameterChoice' D L) (ρ : FamilyRepresentationConstants.RhoFam D) (hK : KillingConditions.KillAt ρ)
    (hSha : TwistedPlaces.ShaFinOdd D) (i : D.nd.Loc) (hTw : TwistedPlaces.TwLoc D i) (hs : D.nd.s0 i = RowSmall.sl D (D.nd.l i)) (π : D.nd.X i)
    (hπ : π ∈ D.nd.Zgood i) (dc : TruncatedSeriesCountingIdentities.Decl D i) (h₁ h₂ h₃ : ℕ) (hh₁ : (h₁ : ℝ) ≤ 4 * RowSmall.hB L)
    (hh₂ : (h₂ : ℝ) ≤ 4 * RowSmall.hB L) (hh₃ : (h₃ : ℝ) ≤ 4 * RowSmall.hB L)
    (hW : ∀ u ∈ dc.col, (Br.h0W i u (ρ i) π : ℝ) ≤
      D.R.r * (c0L (D.nd.l i) D.host.condN h₂ (4 * D.R.n * D.R.nV) : ℝ))
    (hh : (h0 D.nd i dc.col : ℝ) ≤ (D.nd.s0 i : ℝ) + (Nat.log (D.nd.l i) D.R.t : ℝ))
    (hz : ∀ v ∈ D.nd.Q i, D.nd.zeta i v ≠ 1)
    (hconds : EmbeddingTypes.ShaBoundTheoremB i (ρ i) π dc (eL (D.nd.l i) D.host.condN h₁)
      (fun _ => c0L (D.nd.l i) D.host.condN h₂ (4 * D.R.n * D.R.nV))
      (cBL (D.nd.l i) D.host.condN h₃ (4 * D.R.n * D.R.nV) D.R.t)) :
    Bd ρ i π (costC L 6000 30000 (D.nd.l i)) := by
  have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have hy := one_le_hB L P
  have hN : (D.host.condN : ℝ) ≤ 8 * RowSmall.hB L := by linarith [condN_le_hB L P]
  obtain ⟨r1, r2, r3, r4, r5, r6, -⟩ := Num.ranks D
  have ha : (1 : ℝ) ≤ D.R.f * D.R.nV := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
  have hn : ((4 * D.R.n * D.R.nV : ℕ) : ℝ) = 2 * (D.R.f * D.R.nV) := by
    have e : D.R.f = 2 * D.R.n := rfl
    rw [e]; push_cast; ring
  have k0 := Num.cyclotomicWeightExponent_le hl.two_le hy hh₂ hN (n := 4 * D.R.n * D.R.nV) ha (by rw [hn]; linarith)
  have kB := Num.cBL_le hl.two_le hy hh₃ hN (n := 4 * D.R.n * D.R.nV) (t := D.R.t) ha hn.le
    (by have : (1 : ℝ) ≤ D.R.t := by linarith
        exact_mod_cast this)
  have kE := Num.eL_le hl.two_le hy hh₁ hN
  have kl := Num.natLog_le_lam hl.two_le (Num.one_le_sN (D.nd.l i) D.host.condN) hy (n := D.R.t)
    (by linarith [t_le_hB L P])
  have ks := Num.s_le_lam (s := sN (D.nd.l i) D.host.condN) hl.two_le hy
  have hΛ := Num.one_le_lam (s := sN (D.nd.l i) D.host.condN) hl.two_le hy
  rw [← lam_eq] at k0 kB kl ks hΛ
  have h := bound_smallPrime_of_splitBound L P ρ hK hSha i hTw hs π hπ dc _ _ _ (c := 1000) (by norm_num) kE
    (fun u _ => by rw [mul_assoc 1000]; exact k0)
    (fun u hu => (hW u hu).trans (by
      have := mul_le_mul_of_nonneg_left k0 (Nat.cast_nonneg (α := ℝ) D.R.r)
      linarith))
    (by linarith) (by rw [hs, sl_eq] at hh; linarith) hz hconds
  norm_num at h
  exact h

theorem bound_smallPrime_of_splitBound_cyclotomic (L : SizeData₂ D) (P : ParameterChoice' D L) (ρ : FamilyRepresentationConstants.RhoFam D) (hK : KillingConditions.KillAt ρ)
    (hSha : TwistedPlaces.ShaFinOdd D) (i : D.nd.Loc) (hTw : TwistedPlaces.TwLoc D i) (hs : D.nd.l i ∈ D.host.small) (π : D.nd.X i)
    (hπ : π ∈ D.nd.Zgood i) (dc : TruncatedSeriesCountingIdentities.Decl D i) (h₁ h₂ h₃ : ℕ) (hh₁ : (h₁ : ℝ) ≤ 4 * RowSmall.hB L)
    (hh₂ : (h₂ : ℝ) ≤ 4 * RowSmall.hB L) (hh₃ : (h₃ : ℝ) ≤ 4 * RowSmall.hB L)
    (hW : ∀ u ∈ dc.col, (Br.h0W i u (ρ i) π : ℝ) ≤
      D.R.r * (c0L (D.nd.l i) D.host.condN h₂ (4 * D.R.n * D.R.nV) : ℝ))
    (hh : (h0 D.nd i dc.col : ℝ) ≤ (D.nd.s0 i : ℝ) + (Nat.log (D.nd.l i) D.R.t : ℝ))
    (hz : ∀ v ∈ D.nd.Q i, D.nd.zeta i v ≠ 1)
    (hconds : EmbeddingTypes.ShaBoundTheoremB i (ρ i) π dc (eL (D.nd.l i) D.host.condN h₁)
      (fun _ => c0L (D.nd.l i) D.host.condN h₂ (4 * D.R.n * D.R.nV))
      (cBL (D.nd.l i) D.host.condN h₃ (4 * D.R.n * D.R.nV) D.R.t)) :
    Bd ρ i π (costC L 6000 30000 (D.nd.l i)) :=
  bound_smallPrime_of_splitBound_cyclotomic_of_level_eq L P ρ hK hSha i hTw (localLevel_eq_smallPrimeLevel i hs) π hπ dc h₁ h₂ h₃ hh₁ hh₂ hh₃ hW hh hz hconds

end UpperTheory.N

end
end
