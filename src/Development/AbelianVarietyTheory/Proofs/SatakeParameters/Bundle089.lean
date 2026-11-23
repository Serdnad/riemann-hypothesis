module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle087
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TcoMem
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThickLetterWordLatticeSurjectionHypotheses
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle084
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle082
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle083
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.H1H2LocalDuality
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleOfTheorem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle316
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
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.inertPrime_nonthick_letter_no_three_thick : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG), 3 ≤ H.Lw → φ.1.2 = -1 → ¬ (φ = R.cc ∧ Thick H τ) → NoThree (fun i : ZMod (orderOf φ) => Thick H (letter τ φ i)) ∧ ∃ i : ZMod (orderOf φ), ¬ Thick H (letter τ φ i) := by
  first | exact @GlobalTheory.HTW.InertWord.inert_nothree_nonthick | exact GlobalTheory.HTW.InertWord.inert_nothree_nonthick | (intros; apply GlobalTheory.HTW.InertWord.inert_nothree_nonthick <;> assumption)
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

private theorem cast_succ_div_two_of_odd {t : ℕ} (ht : Odd t) :
    (((t + 1) / 2 : ℕ) : ℝ) = ((t : ℝ) + 1) / 2 := by
  obtain ⟨k, rfl⟩ := ht
  have h : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  rw [h]
  push_cast
  ring

theorem _root_.GlobalTheory.HTW.wHat_le : ∀ {D : _root_.Formalism.BasicNotions.D7} (L : _root_.Formalism.BasicNotions.SizeData₂ D) (C : ℝ),
    _root_.GlobalTheory.HTW.Roomy L C →
    (_root_.GlobalTheory.HTW.wHat D : ℝ) = _root_.GlobalTheory.HTW.wMax D + ((D.R.t : ℝ) + 1) / 2 ∧
    (_root_.GlobalTheory.HTW.wHat D : ℝ) + (L.etaSz + D.R.t + 2) ≤ 2 * L.sc.b' ∧
    (_root_.GlobalTheory.HTW.wHat D : ℝ) + _root_.GlobalTheory.HTW.sHat L + _root_.GlobalTheory.HTW.etaHat L + 1
      ≤ 2 * L.sc.b' := by
  intro D L C hL
  have hw : (_root_.GlobalTheory.HTW.wHat D : ℝ) =
      _root_.GlobalTheory.HTW.wMax D + ((D.R.t : ℝ) + 1) / 2 := by
    unfold _root_.GlobalTheory.HTW.wHat
    push_cast [cast_succ_div_two_of_odd D.R.t_odd]
    rfl
  have hmax := (_root_.GlobalTheory.HTW.wMax_le_and_ge L C hL).1
  have hR := hL
  unfold _root_.GlobalTheory.HTW.Roomy at hR
  obtain ⟨-, -, h3, h4, -, -⟩ := hR
  have hS := L.Sc_pos
  have hE := L.etaSz_pos
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hfS : (_root_.GlobalTheory.HTW.sHat L : ℝ) ≤ L.Sc := by
    unfold _root_.GlobalTheory.HTW.sHat
    exact Nat.floor_le hS.le
  have hfE : (_root_.GlobalTheory.HTW.etaHat L : ℝ) ≤ L.etaSz + D.R.t + 2 := by
    unfold _root_.GlobalTheory.HTW.etaHat
    push_cast
    linarith [Nat.floor_le hE.le]
  refine ⟨hw, ?_, ?_⟩
  · rw [hw]; nlinarith
  · rw [hw]; nlinarith

end GlobalTheory.HTW
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.maxSizeAtNonThickPlace_le_and_bound : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ), Roomy L C → (wMax D : ℝ) ≤ 8 / 5 * L.sc.b' ∧ ∀ (g : D.R.GG) (j : Fin D.R.m), ¬ Thick D.host g → ⌊(hcAt D g).e j⌋ ≤ (wMax D : ℤ) := by
  first | exact @GlobalTheory.HTW.wMax_le_and_ge | exact GlobalTheory.HTW.wMax_le_and_ge | (intros; apply GlobalTheory.HTW.wMax_le_and_ge <;> assumption)
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.longOrbit_thickLetters_clusters_and_length : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG) (j : ℕ), 4 * H.Lw < orderOf φ.2 → 1 ≤ j → 2 * j + 2 ≤ H.Lw → Clusters (fun i : ZMod (orderOf φ) => Thick H (letter τ φ i)) j ∧ j + 1 ≤ orderOf φ := by
  first | exact @GlobalTheory.long_clusters | exact GlobalTheory.long_clusters | (intros; apply GlobalTheory.long_clusters <;> assumption)
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.roomy_of_large_scale : ∀ eps C A : ℝ, 0 < eps → 100 ≤ C → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L), L.sc.eps = eps → P.CLw ≤ A → x0 ≤ L.sc.x → Roomy L C := by
  first | exact @GlobalTheory.HTW.roomy_of_large | exact GlobalTheory.HTW.roomy_of_large | (intros; apply GlobalTheory.HTW.roomy_of_large <;> assumption)
end

section

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

theorem _root_.GlobalTheory.T.hOneTwo_of_localFiniteness_tateDuality_eulerChar : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ D : D7, HOneTwo D := by
  first | exact @GlobalTheory.HOneTwoLevel.hOneTwo_holds | exact GlobalTheory.HOneTwoLevel.hOneTwo_holds | (intros; apply GlobalTheory.HOneTwoLevel.hOneTwo_holds <;> assumption)
end

section

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

namespace GlobalTheory.StringRepresentationDecomposition

theorem rbEx_of_jointCond_rho : ∀ D : D7, GlobalDatumResidualRepCondition D → RbEx D := by
  intro D hrho i hHG
  obtain ⟨x, hx⟩ := hHG
  have hx' := hx
  obtain ⟨-, Sig, hSig, hgood⟩ := hx'
  obtain ⟨ρ₀, ξ, -, -, hρx⟩ := hrho i x hx Sig hSig hgood
  exact ⟨_, isRhoBar_of_isRhoOf D i x _ hρx⟩

end GlobalTheory.StringRepresentationDecomposition
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

noncomputable section

namespace GlobalTheory.HTW.Rec

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem filV_succ_le (a : ℤ) : FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  rintro x ⟨y, rfl⟩
  have hle : (PD.Fil (a + 1)).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp := PD.Fil_anti a
  have hc : (TensorProduct.AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
      ((PD.Fil a).restrictScalars Qp).subtype).comp
      (TensorProduct.AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (Submodule.inclusion hle)) =
      TensorProduct.AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
        ((PD.Fil (a + 1)).restrictScalars Qp).subtype := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro v b
    rfl
  exact ⟨TensorProduct.AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (Submodule.inclusion hle) y,
    LinearMap.congr_fun hc y⟩

theorem fildR_succ_le (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    FildR PD ρ τ (a + 1) ≤ FildR PD ρ τ a :=
  inf_le_inf_left _ (filV_succ_le PD a)

theorem fildR_le_DdR (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    FildR PD ρ τ a ≤ DdR PD ρ :=
  inf_le_left.trans inf_le_left

theorem multV_ne_zero_of_jump (ρ : Representation LL G V) [Module.Finite LL ↥(DdR PD ρ)]
    (τ : K →ₐ[Qp] LL) (a : ℤ) (h : IsJumpV PD ρ τ a) : multV PD ρ τ a ≠ 0 := by
  intro h0
  apply h
  haveI : FiniteDimensional LL ↥(FildR PD ρ τ a) :=
    Submodule.finiteDimensional_of_le (fildR_le_DdR PD ρ τ a)
  refine Submodule.eq_of_le_of_finrank_eq (fildR_succ_le PD ρ τ a) ?_
  unfold multV at h0
  omega

end General

theorem jump_multV_ne_zero : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (T : Lat K LL),
    Formalism.MainNotions.LocalSituation.fontCore (P.PD K) → ∀ τ u, IsJumpV (P.PD K) T.ρ τ u → multV (P.PD K) T.ρ τ u ≠ 0 := by
  intro l _ P K LL T hF τ u hJ
  let A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) :=
    { V := T.V, ρ := T.ρ, cont := T.cont }
  obtain ⟨-, ⟨hfin, -⟩, -⟩ := hF ↥LL.1 ↥(OL LL) (GlobalTheory.T.goodCoefficientRing_integers_padicFiniteExtension l LL) A
  haveI : Module.Finite ↥LL.1 ↥(DdR (P.PD K) T.ρ) := hfin
  exact multV_ne_zero_of_jump (P.PD K) T.ρ τ u hJ

end GlobalTheory.HTW.Rec
end
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential

theorem _root_.GlobalTheory.T.trace_cechCochain_fraction_eq_sum_fibre : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ (ρ : F →ₗ[k] k), IsRes k x ρ → IsAlgClosed k → IsReduced ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) → ∀ h : (rB k K x {0}), trF k τ ρ (locCoch k K x h Finset.univ) = ∑ᶠ e : fib k K x, e.1 h := by
  first | (exact @GlobalTheory.PD.trF_locCoch_eq_finsum_fib) | (exact GlobalTheory.PD.trF_locCoch_eq_finsum_fib) | (intros; apply GlobalTheory.PD.trF_locCoch_eq_finsum_fib  <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.thickLetterWord_hypotheses_of_common_conditions : ∀ {D : D7} (L : SizeData₂ D) (HW : HWOf D.loc) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL) (Wd : NWord (RecS.nLet i w hw)), D.nd.l i ≠ 2 → RecS.WordBase L HW i r ρ π w hw Cx hG Wd → RecS.ThickLetterWordLatticeSurjectionHypotheses HW i r ρ π w hw Cx hG Wd := by
  first | exact @GlobalTheory.HTW.RecS.setting_of_wordBase | exact GlobalTheory.HTW.RecS.setting_of_wordBase | (intros; apply GlobalTheory.HTW.RecS.setting_of_wordBase <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.alternatingWord_hypotheses_every_lattice_surjection : ∀ {D : D7} (L : SizeData₂ D) (HW : HWOf D.loc) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL) (Wd : NWord (RecS.nLet i w hw)) (d : ℕ), 11 ≤ D.nd.l i → RecS.WordBase L HW i r ρ π w hw Cx hG Wd → WordsAT (D.nd.l i) Wd d → RecS.AlternatingWordLatticeSurjectionHypotheses HW i r ρ π w hw Cx hG Wd d := by
  first | exact @GlobalTheory.HTW.RecS.settingC_of_wordsAT | exact GlobalTheory.HTW.RecS.settingC_of_wordsAT | (intros; apply GlobalTheory.HTW.RecS.settingC_of_wordsAT <;> assumption)
end

section

open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys

noncomputable section

namespace GlobalTheory.ParRead

open ValuativeRel Matrix

variable {g : ℕ} [Fact g.Prime] {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

theorem lt_one_mem_nhds : {x : F | valuation F x < 1} ∈ nhds (0 : F) :=
  (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨1, by simp⟩

theorem val_lt_one {e : ℚ_[g] ≃+* F} (he : Continuous e) {z : ℚ_[g]} (hz : ‖z‖ < 1) :
    valuation F (e z) < 1 := by
  have h1 : Filter.Tendsto (fun n : ℕ => (e z) ^ n) Filter.atTop (nhds 0) := by
    have := (he.tendsto 0).comp (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz)
    rw [map_zero] at this
    simpa [Function.comp_def, map_pow] using this
  obtain ⟨n, hn⟩ := (h1.eventually lt_one_mem_nhds).exists
  rw [map_pow] at hn
  by_contra hc
  exact absurd hn (not_lt.2 (one_le_pow₀ (not_lt.1 hc)))

theorem val_lt_one_of_red {e : ℚ_[g] ≃+* F} (he : Continuous e) {z : ℤ_[g]}
    (hz : PadicInt.toZMod z = 0) : valuation F (e z) < 1 := by
  have : z ∈ RingHom.ker (PadicInt.toZMod (p := g)) := hz
  rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at this
  exact val_lt_one he this

theorem val_le_one {e : ℚ_[g] ≃+* F} (he : Continuous e) (z : ℤ_[g]) : valuation F (e z) ≤ 1 := by
  set m : ℕ := (PadicInt.toZMod z).val
  have hm : PadicInt.toZMod (z - (m : ℤ_[g])) = 0 := by
    rw [map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  have e1 : e (z : ℚ_[g]) = (m : F) + e ((z - (m : ℤ_[g]) : ℤ_[g]) : ℚ_[g]) := by
    rw [PadicInt.coe_sub, map_sub, PadicInt.coe_natCast, map_natCast]; ring
  rw [e1]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ (val_lt_one_of_red he hm).le)
  clear e1 hm
  induction m with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ]; exact (Valuation.map_add _ _ _).trans (max_le ih (by simp))

def intHom {e : ℚ_[g] ≃+* F} (he : Continuous e) : ℤ_[g] →+* 𝒪[F] :=
  (e.toRingHom.comp (algebraMap ℤ_[g] ℚ_[g])).codRestrict 𝒪[F] fun z => by
    rw [Valuation.mem_integer_iff]; exact val_le_one he z

theorem map_inc_mem_KO {e : ℚ_[g] ≃+* F} (he : Continuous e) {n : ℕ} (k : GL (Fin n) ℤ_[g]) :
    Matrix.GeneralLinearGroup.map e.toRingHom (inc g n k) ∈ GlobalTheory.SplitWeil.KO F (Fin n) := by
  refine ⟨Matrix.GeneralLinearGroup.map (intHom he) k, ?_⟩
  ext i j
  simp [inc, intHom]
  rfl

theorem act_inc {e : ℚ_[g] ≃+* F} (he : Continuous e) {ξ : Fˣ →* ℂˣ} {χ : (ZMod g)ˣ →* ℂˣ}
    (hT : TamePart (ξ.comp (Units.map e.toMonoidHom)) χ) {r t : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin (r + t)) F) V} {u : V} (hu : GlobalTheory.SplitRead.IsBlockVec ξ ρ u)
    (k : GL (Fin (r + t)) ℤ_[g]) (h0 : InPar r (red g (r + t) k : Mt g (r + t)))
    (h1 : tl r (red g (r + t) k : Mt g (r + t)) = 1) (c : (ZMod g)ˣ)
    (hc : (c : ZMod g) = (br r t (red g (r + t) k : Mt g (r + t))).det) :
    ρ (Matrix.GeneralLinearGroup.map e.toRingHom (inc g (r + t) k)) u = ((χ c : ℂˣ) : ℂ) • u := by
  have hred : ∀ i j, (red g (r + t) k : Mt g (r + t)) i j = PadicInt.toZMod ((k : Matrix (Fin (r + t)) (Fin (r + t)) ℤ_[g]) i j) :=
    fun i j => by simp [red]
  have hent : ∀ i j, (Matrix.GeneralLinearGroup.map e.toRingHom (inc g (r + t) k)).val i j =
      e ((k : Matrix (Fin (r + t)) (Fin (r + t)) ℤ_[g]) i j : ℚ_[g]) := fun i j => by simp [inc]
  set d : ℤ_[g] := ((k : Matrix (Fin (r + t)) (Fin (r + t)) ℤ_[g]).submatrix (Fin.natAdd r) (Fin.natAdd r)).det with hd
  have hbr : br r t (red g (r + t) k : Mt g (r + t)) =
      (PadicInt.toZMod (p := g)).mapMatrix ((k : Matrix (Fin (r + t)) (Fin (r + t)) ℤ_[g]).submatrix (Fin.natAdd r) (Fin.natAdd r)) := by
    ext i j
    have hi : r + (i : ℕ) < r + t := by omega
    have hj : r + (j : ℕ) < r + t := by omega
    simp only [br, Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos (And.intro hi hj), hred]
    rfl
  have hdc : PadicInt.toZMod d = c := by rw [hc, hbr, hd, RingHom.map_det]
  have hdu : IsUnit d := by
    by_contra h
    have : d ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by rw [PadicInt.ker_toZMod]; exact h
    rw [RingHom.mem_ker, hdc] at this
    exact c.ne_zero this
  refine (hu _ (map_inc_mem_KO he k) ?_ ?_
    (Units.map e.toMonoidHom (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom hdu.unit)) ?_).trans ?_
  · intro i j
    rw [hent]
    apply val_lt_one_of_red he
    rw [← hred]
    exact h0 _ _ (by simp) (by simp)
  · intro i j
    rw [hent]
    have hij : (red g (r + t) k : Mt g (r + t)) (Fin.castAdd t i) (Fin.castAdd t j) = (1 : Mt g r) i j := by
      rw [← h1]
      have hi : (i : ℕ) < r + t := by omega
      have hj : (j : ℕ) < r + t := by omega
      simp only [tl, Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos (And.intro hi hj)]
      rfl
    have h2 : PadicInt.toZMod ((k : Matrix (Fin (r + t)) (Fin (r + t)) ℤ_[g]) (Fin.castAdd t i) (Fin.castAdd t j) -
        if i = j then 1 else 0) = 0 := by
      rw [map_sub, ← hred, hij, Matrix.one_apply]
      split_ifs <;> simp
    have := val_lt_one_of_red he h2
    convert this using 2
    split_ifs <;> simp
  · simp [hd, RingHom.map_det]
    congr 1
  · have h2 := hT hdu.unit
    have h3 : Units.map (PadicInt.toZMod (p := g)).toMonoidHom hdu.unit = c := Units.ext (by simpa using hdc)
    rw [h3, MonoidHom.comp_apply] at h2
    rw [h2]

theorem inPar_one {r n : ℕ} : InPar r (1 : Mt g n) := fun i j hj hi => by
  rw [Matrix.one_apply_ne]
  intro h; rw [h] at hi; omega

theorem tl_one {r t : ℕ} : tl r (1 : Mt g (r + t)) = 1 := by
  ext i j
  have hi : (i : ℕ) < r + t := by omega
  have hj : (j : ℕ) < r + t := by omega
  simp only [tl, Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos (And.intro hi hj), Matrix.one_apply, Fin.ext_iff]

theorem br_one {r t : ℕ} : br r t (1 : Mt g (r + t)) = 1 := by
  ext i j
  have hi : r + (i : ℕ) < r + t := by omega
  have hj : r + (j : ℕ) < r + t := by omega
  simp only [br, Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos (And.intro hi hj), Matrix.one_apply, Fin.ext_iff]
  by_cases h : (i : ℕ) = j
  · simp [h]
  · rw [if_neg (by omega), if_neg h]

theorem blk_parts {r t : ℕ} (y : Gn g t) :
    InPar r (blk r t (r + t) 1 y : Mt g (r + t)) ∧ tl r (blk r t (r + t) 1 y : Mt g (r + t)) = 1 ∧
      br r t (blk r t (r + t) 1 y : Mt g (r + t)) = (y : Mt g t) := by
  set M : Mt g (r + t) := fun i j : Fin (r + t) =>
    if (i : ℕ) < r ∧ (j : ℕ) < r then Formalism.MainNotions.ArithmeticCylinders.entN ((1 : Gn g r) : Mt g r) i j
    else if r ≤ (i : ℕ) ∧ r ≤ (j : ℕ) then Formalism.MainNotions.ArithmeticCylinders.entN (y : Mt g t) (i - r) (j - r) else 0 with hM
  have h0 : InPar r M := fun i j hj hi => by rw [hM]; dsimp only; rw [if_neg (by omega), if_neg (by omega)]
  have h1 : tl r M = 1 := by
    ext i j
    have hi : (i : ℕ) < r + t := by omega
    have hj : (j : ℕ) < r + t := by omega
    simp [tl, Formalism.MainNotions.ArithmeticCylinders.entN, hM, hi, hj]
  have h2 : br r t M = y := by
    ext i j
    simp [br, Formalism.MainNotions.ArithmeticCylinders.entN, hM]
  have hu : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, LabelDet.det_inPar r t M h0, h1, h2, Matrix.det_one, one_mul]
    exact (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
  have hb : (blk r t (r + t) 1 y : Mt g (r + t)) = M := by
    show ((toG M : Gn g (r + t)) : Mt g (r + t)) = M
    rw [toG, dif_pos hu]; rfl
  rw [hb]; exact ⟨h0, h1, h2⟩

theorem isParVec_of_isBlockVec : ∀ (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F), Continuous e → ∀ (ξ : Fˣ →* ℂˣ) (χ : (ZMod g)ˣ →* ℂˣ),
    TamePart (ξ.comp (Units.map e.toMonoidHom)) χ → ∀ (r t : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin (r + t)) F) V) (u : V), GlobalTheory.SplitRead.IsBlockVec ξ ρ u →
    IsParVec (ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) r t χ u := by
  intro g _ F _ _ _ _ e he ξ χ hT r t V _ _ ρ u hu
  have hsurj : ∀ x : Gn g (r + t), red g (r + t) (Function.invFun (red g (r + t)) x) = x :=
    fun x => Function.invFun_eq (Model.red_surjective _ x)
  refine ⟨?_, ?_, ?_⟩
  · rw [Model.mem_principalCongruenceFixedVectors_iff]
    intro k hk
    have := act_inc he hT hu k (by rw [hk, Units.val_one]; exact inPar_one) (by rw [hk, Units.val_one]; exact tl_one) 1
      (by rw [hk, Units.val_one, Units.val_one, br_one, Matrix.det_one])
    rw [map_one, Units.val_one, one_smul] at this
    exact this
  · intro x h0 h1 h2
    have := act_inc he hT hu (Function.invFun (red g (r + t)) x) (by rw [hsurj]; exact h0) (by rw [hsurj]; exact h1) 1
      (by rw [hsurj, h2, Matrix.det_one, Units.val_one])
    rw [map_one, Units.val_one, one_smul] at this
    exact this
  · intro y
    obtain ⟨h0, h1, h2⟩ := blk_parts (r := r) y
    have := act_inc he hT hu (Function.invFun (red g (r + t)) (blk r t (r + t) 1 y)) (by rw [hsurj]; exact h0)
      (by rw [hsurj]; exact h1) (Matrix.GeneralLinearGroup.det y)
      (by rw [hsurj, h2, Matrix.GeneralLinearGroup.val_det_apply])
    exact this

end GlobalTheory.ParRead
end
end
