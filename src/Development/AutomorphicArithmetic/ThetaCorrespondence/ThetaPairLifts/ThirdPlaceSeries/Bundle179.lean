module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle115
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterMtEqSmulOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle476
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle177
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle360
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle488
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle632
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle172
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle092
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle155
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle166
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle173
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle174
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle171
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle467
public import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle002
public import Development.AutomorphicArithmetic.ResidueCharacters.NumCost
import Development.AutomorphicArithmetic.ResidueCharacters.NumParameters
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section

section



section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
namespace GlobalTheory.MiTop

theorem centralRatio_stab_atT_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ u u' (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (f' : _root_.GlobalTheory.Fam.FamilyCharacter W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → _root_.GlobalTheory.MiTop.PlacedConditions f' B' → ∀ a₀ a a₀' a', _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → _root_.GlobalTheory.MiTop.IsTranslate' f' B' a₀' a' → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ k ∈ _root_.GlobalTheory.MiTop.rJ_z W, _root_.GlobalTheory.MiTop.translationElement f B a₀ a = z * _root_.GlobalTheory.MiTop.translationElement f' B' a₀' a' * k → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) → ((((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ∨ (((D.mem u').A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) → GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v z ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig (D.sp.Y 0).gram ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) v := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr u u' f f' B B' hP hP' a₀ a a₀' a' hA hA' z hzf hzc k hk he v hv hTv
  have hm : 0 < D.R.m := by have := D.R.rS_two; omega
  obtain ⟨hsd, hfr⟩ := _root_.GlobalTheory.Fam.sdY_frames_alt W hW 0 hm
  have hFG : ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0).FG := hsd.1.fg
  have hkSt : Formalism.IndefR.Lev.finE (Yc D 0) k ∈ Formalism.L2.DIV.St ((_root_.GlobalTheory.Fam.pk_z W).βY 0) :=
    Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hk.2)
  have hkM : Moves (D.sp.Y 0) k ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) (· = v) :=
    (GlobalTheory.StMoves.moves_iff_stabLoc _ _ hFG v k).2
      ((GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D (Yc D 0) _ _ hfr k).1 hkSt v)
  obtain ⟨c, hc⟩ := GlobalTheory.CenterScalar.center_mt_eq_smul_one D (D.sp.Y 0) z⁻¹ (Subgroup.inv_mem _ hzc)
  have hmul : ∀ g h : GA D (D.sp.Y 0), Formalism.L2.Theta.mt _ (g * h) = Formalism.L2.Theta.mt _ g * Formalism.L2.Theta.mt _ h :=
    fun g h => by simp [Formalism.L2.Theta.mt, map_mul]
  have hone : Formalism.L2.Theta.mt (D.sp.Y 0) 1 = 1 := by simp [Formalism.L2.Theta.mt, map_one]
  have h3 := _root_.GlobalTheory.T.placed_bessel_translate_vector_alt W hW hr u f B hP a₀ a hA
  have h3' := _root_.GlobalTheory.T.placed_bessel_translate_vector_alt W hW hr u' f' B' hP' a₀' a' hA'
  have h4 := _root_.GlobalTheory.T.placed_bessel_pair_vector_alt W hW hr u u' f f' B B' hP hP' a₀ a a₀' a' hA hA' v hv hTv
  have h5 := GlobalTheory.coord_first_isotropic_ne_zero W.S.X W.Q.instEq hr
  generalize _root_.GlobalTheory.MiTop.translationElement f B a₀ a = t at he h3
  generalize _root_.GlobalTheory.MiTop.translationElement f' B' a₀' a' = t' at he h3'
  have hunit : IsUnit (Formalism.L2.Theta.mt (D.sp.Y 0) t'⁻¹) :=
    ⟨⟨Formalism.L2.Theta.mt (D.sp.Y 0) t'⁻¹, Formalism.L2.Theta.mt (D.sp.Y 0) t', by rw [← hmul, inv_mul_cancel, hone], by rw [← hmul, mul_inv_cancel, hone]⟩, rfl⟩
  have hkey : t'⁻¹ * z⁻¹ = k * t⁻¹ := by rw [he]; group
  have hMinv : Moves (D.sp.Y 0) z⁻¹ ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) (· = v) := by
    intro y hy
    rw [hc, Matrix.smul_mulVec, Matrix.one_mulVec]
    refine GlobalTheory.LineUnit.smul_mem_latV_iff D (D.sp.Y 0) _
      (by
        have hfull := GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hsd
        first | exact hfull | exact hfull.toIsLattice) v _ h5 c _ hunit ?_ y hy
    intro b hb
    have h3b := h3 b
    have h3b' := h3' b
    have h4b := h4 b hb
    generalize hw : (fun i => b * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i)))) = w at h3b h3b' h4b
    have hsupp : ∀ i, w i ∈ GlobalTheory.FinPl.idAt D (· = v) := fun i => by
      rw [← hw]; exact Ideal.mul_mem_right _ _ hb
    have e1 : (fun i => c * (b * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) =
        Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) z⁻¹) w := by
      rw [← hw, hc, Matrix.smul_mulVec, Matrix.one_mulVec]; rfl
    have s1 : Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) t'⁻¹) (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) z⁻¹) w) =
        Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) k) (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) t⁻¹) w) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hmul, ← hmul, hkey]
    have s2 := hkM _ (GlobalTheory.FinPl.KOpen.supp_mulVec _ _ t⁻¹ hsupp)
    rw [e1, s1, ← s2, h3b, h3b']
    exact h4b
  have hM := GlobalTheory.StMoves.moves_inv hMinv
  rw [inv_inv] at hM
  exact (GlobalTheory.StMoves.moves_iff_stabLoc (D.sp.Y 0) _ hFG v z).1 hM
end GlobalTheory.MiTop
end
end

section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.admG2_of_setup_jumps : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ ep, AdmissibleParameterJ.hodgeTateJumpsAtModulesForSign D ep → ∀ i, EmbeddingTypes.admG2 i (X.r i) ep := by
  first | exact @_root_.GlobalTheory.JumpShapeAt.main_alt_alt | exact _root_.GlobalTheory.JumpShapeAt.main_alt_alt | (intros; apply _root_.GlobalTheory.JumpShapeAt.main_alt_alt <;> assumption)
end
end

section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.star_bound_of_paired_character_condition : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ (constantSecondHub C1 : ℝ) (CT : ℕ), 0 ≤ constantSecondHub → 1 ≤ C1 → (CT : ℝ) ≤ L.sc.b → _root_.Formalism.MainNotions.PairedCharacterCondition.PairedCharacterConditionAlt (D := D) constantSecondHub CT → MultLe L → TwistedPlaces.ParametersPolynomiallyBounded L C1 P → SizeG L → StarH L (2000 * (constantSecondHub + 1) + 5 * C1) := by
  first | exact @_root_.GlobalTheory.NLinkTyp.main_alt_alt | exact _root_.GlobalTheory.NLinkTyp.main_alt_alt | (intros; apply _root_.GlobalTheory.NLinkTyp.main_alt_alt <;> assumption)
end
end

section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.exists_hubData_admJ_setup : Hypotheses₂ → ∀ {eps : ℝ} (Fm : FamP eps), ∀ (C C₂ : ℝ) (CT : ℕ), TwGood Fm → _root_.GlobalTheory.NLink.FactsFAlt Fm C CT → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), TwistedPlaces.ShaFinOdd (Fm.D x i) → ∀ exc : Finset ℕ, ∃ (HW : HWOf (Fm.D x i).loc) (F : FonOf (Fm.D x i).loc (Fm.D x i).locA HW) (_ : CmpOf (Fm.D x i).loc (Fm.D x i).locA HW F) (X : KillingConditions.HubData (Fm.D x i)), X.exc = exc ∧ _root_.Formalism.MainNotions.AdmissibleParameterJ.AdmJAlt (Fm.L x i) ∧ _root_.GlobalTheory.NLink.SetupAlt (Fm.L x i) (Fm.ex x hx i).nch HW X C₂ := by
  first | exact @_root_.GlobalTheory.NLink.exists_setup_large_alt | exact _root_.GlobalTheory.NLink.exists_setup_large_alt | (intros; apply _root_.GlobalTheory.NLink.exists_setup_large_alt <;> assumption)
end
end

section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.invariantsBoundNonsplit_of_setup : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → KillingConditions.InvariantsBoundsWithCoarseColumnConstant L X 120 := by
  first | exact @_root_.GlobalTheory.NSizes.main_alt_alt | exact _root_.GlobalTheory.NSizes.main_alt_alt | (intros; apply _root_.GlobalTheory.NSizes.main_alt_alt <;> assumption)
end
end

section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.hodgeJumpParameters_of_setup : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ ep, AdmissibleParameterJ.hodgeTateJumpsAtModulesForSign D ep → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes X.r ep L := by
  first | exact @_root_.GlobalTheory.HostJumpWin.main_alt_alt | exact _root_.GlobalTheory.HostJumpWin.main_alt_alt | (intros; apply _root_.GlobalTheory.HostJumpWin.main_alt_alt <;> assumption)
end
end

section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace UpperTheory.N
theorem mid_of_rowOn_alt (Q : D7 → ℕ → Prop)
    (hQ : ∀ D l, l.Prime → Q D l → D.host.condN.factorization l = D.host.QS.factorization l)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (h : _root_.UpperTheory.N.RowOnAlt Q A B) {eps : ℝ} (Fm : FamP eps) :
    ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x)
      (HW : HWOf (Fm.D x i).loc) (F : FonOf (Fm.D x i).loc (Fm.D x i).locA HW)
      (_ : CmpOf (Fm.D x i).loc (Fm.D x i).locA HW F) (X : KillingConditions.HubData (Fm.D x i)) (C₂ : ℝ),
      _root_.GlobalTheory.NLink.SetupAlt (Fm.L x i) (Fm.ex x hx i).nch HW X C₂ → ∀ k, TwistedPlaces.TwLoc (Fm.D x i) k → Q (Fm.D x i) ((Fm.D x i).nd.l k) →
        ∀ π ∈ (Fm.D x i).nd.Zgood k, Bd X.ρ k π (midF (Fm.L x i) C) := by
  obtain ⟨x0, h0⟩ := h Fm
  obtain ⟨C0, x1, hC0, hpar⟩ := GlobalTheory.T.admissible_parameters_family_const Fm
  refine ⟨18 * A * C0 + 2 * B * (3 * C0 + 9) + 5 * C0 + 1, max 3 (max x0 x1), ?_,
    fun x hxx hx i HW F Cm X C₂ hS k hTw hq π hπ => ?_⟩
  · have : 0 ≤ C0 := by linarith
    positivity
  have h3 : 3 ≤ x := (le_max_left _ _).trans hxx
  have hb := h0 x (((le_max_left _ _).trans (le_max_right _ _)).trans hxx) hx i HW F Cm X C₂ hS k hTw hq π hπ
  obtain ⟨-, -, -, hn, ht, -⟩ := hpar x (((le_max_right _ _).trans (le_max_right _ _)).trans hxx) hx i
  have hlog : 1 ≤ Real.log (Fm.L x i).sc.x := by
    rw [Fm.L_x x i hx, Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hl : ((Fm.D x i).nd.l k).Prime := ((Fm.D x i).nd.lPrime k).out
  have hc : costC (Fm.L x i) A B ((Fm.D x i).nd.l k) ≤
      midF (Fm.L x i) (18 * A * C0 + 2 * B * (3 * C0 + 9) + 5 * C0 + 1) :=
    Num.cost_le' (Fm.L x i) (Fm.params x hx i) hA hB hC0 hlog hn ht hl (hQ _ _ hl hq) le_rfl
  unfold Bd at hb ⊢
  linarith
theorem boundAtTwoThree_of_local_bounds_at_two_three (h3qd : ∀ D : D7, 3 ≠ D.host.q ∧ 3 ≠ D.host.d)
    (h2 : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ _root_.UpperTheory.N.SecondBoundCondition A B) (h3 : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ _root_.UpperTheory.N.ThirdBoundCondition A B)
    {eps : ℝ} (Fm : FamP eps) : _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm := by
  obtain ⟨A, B, hA, hB, h2⟩ := h2
  obtain ⟨A', B', hA', hB', h3⟩ := h3
  obtain ⟨C, x0, hC, h2⟩ := _root_.UpperTheory.N.mid_of_rowOn_alt (fun _ l => l = 2) (fun D l _ (e : l = 2) =>
    Num.factorization_condN D (by rw [e]; exact UpperTheory.Small.two_mem D.host)) A B hA hB (fun Fm => h2 Fm) Fm
  obtain ⟨C', x1, hC', h3⟩ := _root_.UpperTheory.N.mid_of_rowOn_alt (fun D l => l = 3 ∧ l ∉ D.host.small) (fun D l _ (e : l = 3 ∧ l ∉ D.host.small) =>
    Num.factorization_condN' D (by rw [e.1]; exact (h3qd D).1) (by rw [e.1]; exact (h3qd D).2)) A' B' hA' hB' (fun Fm => h3 Fm) Fm
  refine ⟨max C C', max x0 x1, fun x hxx hx i HW F Cm X C₂ hS k hTw hl π hπ => ?_⟩
  have h0 : 0 ≤ max C C' := hC.trans (le_max_left _ _)
  rcases hl with hl | hl
  · have h := h2 x ((le_max_left _ _).trans hxx) hx i HW F Cm X C₂ hS k hTw hl π hπ
    have h' := midF_mono (Fm.L x i) (le_max_left C C') h0
    unfold Bd at h ⊢; linarith
  · have h := h3 x ((le_max_right _ _).trans hxx) hx i HW F Cm X C₂ hS k hTw hl π hπ
    have h' := midF_mono (Fm.L x i) (le_max_right C C') h0
    unfold Bd at h ⊢; linarith
end UpperTheory.N
end
end

section



section
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace UpperTheory.N
variable {D : D7}
end UpperTheory.N
theorem UpperTheory.N.starSF_of_rowC_alt (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) : _root_.UpperTheory.N.RowCAlt A B → _root_.UpperTheory.N.StarSelfDualCondition := by
  intro h eps Fm
  obtain ⟨x0, h0⟩ := h Fm
  obtain ⟨C0, x1, hC0, hpar⟩ := GlobalTheory.T.admissible_parameters_family_const Fm
  refine ⟨18 * A * C0 + 2 * B * (3 * C0 + 9) + 5 * C0 + 1, max 3 (max x0 x1),
    fun x hxx hx i HW F Cm X C₂ hS k hTw hs h2 π hπ => ?_⟩
  have h3 : 3 ≤ x := (le_max_left _ _).trans hxx
  have hb := h0 x (((le_max_left _ _).trans (le_max_right _ _)).trans hxx) hx i HW F Cm X C₂ hS k hTw hs h2 π hπ
  obtain ⟨-, -, -, hn, ht, -⟩ := hpar x (((le_max_right _ _).trans (le_max_right _ _)).trans hxx) hx i
  have hlog : 1 ≤ Real.log (Fm.L x i).sc.x := by
    rw [Fm.L_x x i hx, Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hc : UpperTheory.N.costC (Fm.L x i) A B ((Fm.D x i).nd.l k) ≤
      midF (Fm.L x i) (18 * A * C0 + 2 * B * (3 * C0 + 9) + 5 * C0 + 1) :=
    UpperTheory.N.Num.cost_le (Fm.L x i) (Fm.params x hx i) hA hB hC0 hlog hn ht hs le_rfl
  unfold Bd at hb ⊢
  linarith
end
end
end
