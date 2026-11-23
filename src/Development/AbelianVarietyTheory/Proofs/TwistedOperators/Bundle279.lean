module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle223
public import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle194
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle247
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle172
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle041
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle257
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle267
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle268
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle270
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle271
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle245
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle246
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle269
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOMemFinSub
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexMovedHomLatticeEqProdHalvesSplitPlace
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1714
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle251
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle133
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Topology

noncomputable section

namespace GlobalTheory.GridJoin

variable {D : D7}
theorem conj_back {G : Type*} [Group G] (b g : G) : b⁻¹ * (b * g * b⁻¹) * b = g := by group

theorem mem_princGL_of_cong {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {I : Ideal (𝓞 E)} (h2 : x ∈ St β)
    {z : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hz : ∀ i j, z i j ∈ Formalism.L2.Herm.intAf F E)
    (e : (β⁻¹ * x * β).1 - 1 = Ideal.absNorm I • z) : x ∈ GlobalTheory.Grid.princGL β I := by
  obtain ⟨y, rfl⟩ := h2
  refine GlobalTheory.Grid.mem_princGL.2 ⟨y, rfl, fun i j => ?_⟩
  have e2 : β⁻¹ * frGL β y * β = intGL F E n y := conj_back β _
  rw [e2] at e
  have e3 := congrFun (congrFun e i) j
  have hmem : ((Ideal.absNorm I : ℕ) : Formalism.L2.Herm.intAf F E) ∈ idS F I := by
    rw [← map_natCast (oToS F E)]
    exact Ideal.mem_map_of_mem _ (Ideal.absNorm_mem I)
  have e4 : ((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) - 1) i j = ((Ideal.absNorm I : ℕ) : Formalism.L2.Herm.intAf F E) * ⟨z i j, hz i j⟩ := by
    apply Subtype.ext
    refine Eq.trans ?_ (e3.trans ?_)
    · simp only [Matrix.sub_apply, Matrix.one_apply]
      split_ifs <;> rfl
    · simp [nsmul_eq_mul]
  rw [e4]
  exact Ideal.mul_mem_right _ _ hmem

theorem princ_isOpen (N : GlobalTheory.Grid.Node D) {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) :
    IsOpen (((N.princ I).comap (Lev.finE N.V) : Subgroup (GA D N.V)) : Set (GA D N.V)) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig N.V.gram
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig N.V.gram
  have hf : Continuous (finHom N.V) := (continuous_subtype_val.comp hπ.continuous).congr fun κ => hπ κ
  have hN : Ideal.absNorm I ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 hI
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ N.V N.β ∅,
    GlobalTheory.FunObj.eventually_cong_mat N.β hN hf (map_one _)] with κ ⟨h1, h2, _⟩ ⟨z, hz, e⟩
  exact ⟨h1, mem_princGL_of_cong h2 hz e⟩

theorem princ_isCompact (N : GlobalTheory.Grid.Node D) {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) :
    IsCompact ((Lev.levA N.V (N.princ I) : Subgroup (GA D N.V)) : Set (GA D N.V)) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig N.V.gram
  obtain ⟨C, hC, hCm⟩ := GlobalTheory.ParahoricCompact.exists_compact N.V N.β
  refine hC.of_isClosed_subset ((GlobalTheory.Ker.CongTop.isClosed_GfC N.V).inter
    (Subgroup.isClosed_of_isOpen _ (princ_isOpen N hI))) fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := Lev.mem_levA.1 hk
  exact hCm k hk1 (GlobalTheory.Grid.princGL_top N.β ▸ GlobalTheory.Grid.princGL_mono N.β le_top hk2.2)

theorem exists_isMeasFD (V : HSp D) (hV : V.SigOK) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (ho : IsOpen ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)))
    (hc : IsCompact ((Lev.levA V K : Subgroup (GA D V)) : Set (GA D V))) : ∃ μ 𝓕, Lev.IsMeasFD V K μ 𝓕 := by
  choose m hm using GlobalTheory.MinfMeasure.exists_isMinf
  obtain ⟨μ, hμ⟩ := GlobalTheory.LevelMeasure.exists_isMeasLevW D V hV K ho hc (fun _ m => Lev.IsMinf m) (fun _ => m _ _)
    (fun _ => (hm _ _).1) (fun _ => hm _ _) fun _ _ h => GlobalTheory.LevelMeasure.isMinf_unique (hm _ _) h
  obtain ⟨𝓕, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_fundDom D V μ hμ.1
  exact ⟨μ, 𝓕, hμ, h𝓕⟩

theorem exists_measDat (N : GlobalTheory.Grid.Node D) (hs : N.V.SigOK) (df : Prop) (hdf : df → ∀ τ, (N.V.sig τ).2 = 0)
    {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) : ∃ m : N.MeasDat, m.Is df (N.princ I) := by
  have ho := princ_isOpen N hI
  have hc := princ_isCompact N hI
  by_cases h : df
  · obtain ⟨μ, 𝓕, e⟩ := GlobalTheory.FunObj.exists_meas N.V hs (hdf h) (N.princ I) ⟨ho, hc⟩
    rw [if_pos rfl] at e
    exact ⟨⟨μ, 𝓕⟩, by unfold GlobalTheory.Grid.Node.MeasDat.Is; exact ⟨fun _ => e, fun hn => absurd h hn⟩⟩
  · obtain ⟨μ, 𝓕, e⟩ := exists_isMeasFD N.V hs _ ho hc
    exact ⟨⟨μ, 𝓕⟩, by unfold GlobalTheory.Grid.Node.MeasDat.Is; exact ⟨fun h' => absurd h' h, fun _ => e⟩⟩

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem exists_isMeas (G : GlobalTheory.Grid.GridPre R) (hS : G.IsSpaces) :
    ∃ m00 mV mP mX, (withMeas G m00 mV mP mX).IsMeas := by
  have hlvl : G.lvl R ≠ ⊥ := G.toPlaceDat.ideal_ne_bot R.Pg
  have htop : (⊤ : Ideal (𝓞 D.host.E)) ≠ ⊥ := top_ne_bot
  obtain ⟨m00, h00⟩ := exists_measDat (G.V 0 0) (D.sp.Y_sig 0) False (fun h => h.elim) hlvl
  have hV : ∀ i j, ∃ m : (G.nV i j).MeasDat, i + 1 ≤ D.R.m → j ≤ D.R.m →
      m.Is (if j = 0 then False else D.R.m - 1 ≤ j) ((G.nV i j).princ (if j = 0 then G.lvl R else ⊤)) := by
    intro i j
    by_cases h : i + 1 ≤ D.R.m ∧ j ≤ D.R.m
    · have hN := hS.vert i j h.1 h.2
      obtain ⟨m, hm⟩ := exists_measDat (G.nV i j) hN.sigOK (if j = 0 then False else D.R.m - 1 ≤ j)
        (fun hd τ => by
          rw [hN.sig τ]
          show (D.R.m - j) / 2 = 0
          by_cases hj : j = 0
          · rw [if_pos hj] at hd; exact hd.elim
          · rw [if_neg hj] at hd; omega)
        (I := if j = 0 then G.lvl R else ⊤) (by split_ifs; exacts [hlvl, htop])
      exact ⟨m, fun _ _ => hm⟩
    · exact ⟨⟨0, ∅⟩, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  have hP : ∀ i, ∃ m : (G.P i).MeasDat, i ≤ D.R.m → m.Is (i = D.R.m) ((G.P i).princ (G.lvl R)) := by
    intro i
    by_cases h : i ≤ D.R.m
    · have hN := hS.P i h
      obtain ⟨m, hm⟩ := exists_measDat (G.P i) hN.sigOK (i = D.R.m)
        (fun hd τ => by
          rw [hN.sig τ]
          show (D.R.m - i + 1) / 2 = 0
          omega) hlvl
      exact ⟨m, fun _ => hm⟩
    · exact ⟨⟨0, ∅⟩, fun h1 => absurd h1 h⟩
  have hX : ∀ j, ∃ m : (G.nX j).MeasDat, j + 1 ≤ D.R.m → m.Is True ((G.nX j).princ ⊤) := by
    intro j
    by_cases h : j + 1 ≤ D.R.m
    · have hN := hS.X j h
      obtain ⟨m, hm⟩ := exists_measDat (G.nX j) hN.sigOK True
        (fun _ τ => by
          rw [hN.sig τ]) htop
      exact ⟨m, fun _ => hm⟩
    · exact ⟨⟨0, ∅⟩, fun h1 => absurd h1 h⟩
  choose mV hmV using hV
  choose mP hmP using hP
  choose mX hmX using hX
  refine ⟨m00, mV, mP, mX, ⟨fun i hi => ?_, fun i j hi hj => ?_, fun i hi => hmP i hi, fun j hj => hmX j hj⟩⟩
  · cases i with
    | zero => exact h00
    | succ i =>
      have := hmV i 0 hi (Nat.zero_le _)
      rw [if_pos rfl, if_pos rfl] at this
      exact this
  · have := hmV i (j + 1) hi hj
    rw [if_neg (Nat.succ_ne_zero j), if_neg (Nat.succ_ne_zero j)] at this
    exact this

end GlobalTheory.GridJoin
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.DetTor

variable {D : D7} {S T : HSp D}

theorem det_conj_diag_exp {n : ℕ} {x : Matrix (Fin n) (Fin n) ℂ} (hx : IsUnit x.det) (t : Fin n → ℝ) (k : ℤ) :
    (x * diagonal (fun a => cexp ((t a : ℂ) * I)) * x⁻¹).det ^ k = cexp (((∑ a, (k : ℝ) * t a : ℝ) : ℂ) * I) := by
  rw [Matrix.det_conj ((Matrix.isUnit_iff_isUnit_det x).2 hx), det_diagonal, ← Complex.exp_sum,
    ← Complex.exp_int_mul]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem detPow_mul_torAt (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas) (hB : C.IsB B) (m : D.what₂.Tau → ℤ)
    (ρ : D.what₂.Tau) (t : Fin T.rank → ℝ) (g : GA D T) :
    detPow C.θ T m (g * torAt C.θ T B ρ t) = cexp (((∑ a, ((m ρ : ℤ) : ℝ) * t a : ℝ) : ℂ) * I) * detPow C.θ T m g := by
  have R : GlobalTheory.SmoothForms.RealPoints C.θ T := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 C.θ C.inf T
  have hu := GlobalTheory.HolRead.AdExt.conj_mem_unitary (GlobalTheory.AdSpan.ConjHol.isUnit_det_B C hB ρ) (hB ρ)
    (by unfold sgnM; exact GlobalTheory.HolRead.AdExt.diag_unitary _ t)
  have hk := GlobalTheory.HolRead.AdExt.atTau_spec R ρ hu
  have key : ∀ ρ', (compAt C.θ ρ' (Formalism.L2.Theta.mt T (g * torAt C.θ T B ρ t))).det ^ m ρ' =
      (if ρ' = ρ then cexp (((∑ a, ((m ρ : ℤ) : ℝ) * t a : ℝ) : ℂ) * I) else 1) *
        (compAt C.θ ρ' (Formalism.L2.Theta.mt T g)).det ^ m ρ' := by
    intro ρ'
    have hm : compAt C.θ ρ' (Formalism.L2.Theta.mt T (g * torAt C.θ T B ρ t)) =
        compAt C.θ ρ' (Formalism.L2.Theta.mt T g) * compAt C.θ ρ' (Formalism.L2.Theta.mt T (torAt C.θ T B ρ t)) :=
      R.2.2.2.1 g _ ρ'
    rw [hm, det_mul, mul_zpow, mul_comm]
    congr 1
    by_cases c : ρ' = ρ
    · subst c
      rw [if_pos rfl]
      have h1 : compAt C.θ ρ' (Formalism.L2.Theta.mt T (torAt C.θ T B ρ' t)) =
          B ρ' * diagonal (fun a => cexp ((t a : ℂ) * I)) * (B ρ')⁻¹ := hk.2.1
      rw [h1]
      exact det_conj_diag_exp (GlobalTheory.AdSpan.ConjHol.isUnit_det_B C hB ρ') t (m ρ')
    · rw [if_neg c]
      have h1 : compAt C.θ ρ' (Formalism.L2.Theta.mt T (torAt C.θ T B ρ t)) = 1 := hk.2.2 ρ' c
      rw [h1, det_one, _root_.one_zpow]
  unfold detPow
  rw [Finset.prod_congr rfl fun ρ' _ => key ρ', Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ ρ,
    if_pos (Finset.mem_univ _)]

end GlobalTheory.AdSpan.DetTor

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isFockVacuumAt_reframeFunctionOnHoms : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V), IsInfFam θ → (∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y)) → ∀ (τ : D.what₂.Tau) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ), IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 sT) f → IsFockVacAt (heisO ψ (reS S b) T) θ τ (cplxO 1 sT) (reF S T b f) := by
  first | exact @GlobalTheory.AdSpan.ReVec.FockVac.isFockVacAt_reF | exact GlobalTheory.AdSpan.ReVec.FockVac.isFockVacAt_reF | (intros; apply GlobalTheory.AdSpan.ReVec.FockVac.isFockVacAt_reF <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isSmoothThetaFunction_reframeFunctionOnHoms : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V), (∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y)) → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ (reS S b) T (reF S T b f) := by
  first | exact @GlobalTheory.AdSpan.ReVec.ThetaCarry.isThetaFunO_reF | exact GlobalTheory.AdSpan.ReVec.ThetaCarry.isThetaFunO_reF | (intros; apply GlobalTheory.AdSpan.ReVec.ThetaCarry.isThetaFunO_reF <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.symplecticFormOnHoms_reframeHomMatrix : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (x y : WO (reS S b) T), symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y) := by
  first | exact @GlobalTheory.AdSpan.ReVec.Sympl.symplO_reW | exact GlobalTheory.AdSpan.ReVec.Sympl.symplO_reW | (intros; apply GlobalTheory.AdSpan.ReVec.Sympl.symplO_reW <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_completedLattice_reframeHomMatrix_iff : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (LT : Set (Fin T.rank → D.host.E)) (u : WO (reS S b) T), u ∈ latO (reS S b) T (L0c D (reS S b)) LT (fun _ => True) ↔ reW S T b u ∈ latO S T (L0c D S) LT (fun _ => True) := by
  first | exact @GlobalTheory.AdSpan.ReVec.latO_reW_iff | exact GlobalTheory.AdSpan.ReVec.latO_reW_iff | (intros; apply GlobalTheory.AdSpan.ReVec.latO_reW_iff <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_frameChange_weakWeilRepresentation : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V), ∃ e : GA D (reS S b) ≃* GA D S, (∀ h, e h ∈ GinfC S ↔ h ∈ GinfC (reS S b)) ∧ ∀ (ψ : AddChar (AF D.host.F) ℂ) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak ψ S T om → ContT ψ om → ∃ om' : GA D (reS S b) × GA D T →* Module.End ℂ (WO (reS S b) T → ℂ), IsWeak ψ (reS S b) T om' ∧ ContT ψ om' ∧ ∀ h g f, om' (h, g) (reF S T b f) = reF S T b (om (e h, g) f) := by
  first | exact @GlobalTheory.AdSpan.reframe_weil | exact GlobalTheory.AdSpan.reframe_weil | (intros; apply GlobalTheory.AdSpan.reframe_weil <;> assumption)
end

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll GlobalTheory.TrEll.RealTorus
open scoped TensorProduct ComplexConjugate Matrix

theorem _root_.GlobalTheory.T.torusFieldComplexRoots_norm_eq_one_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (w : InfinitePlace F) (τ : EmbOver E w), Function.Bijective (PsiAll P τ) → CompactSpace (Tor P w.Completion) → ∀ i, ‖cxRoots τ.1 P i‖ = 1 := by
  first | exact @GlobalTheory.TrEll.realTorus_norm_cxRoots | exact GlobalTheory.TrEll.realTorus_norm_cxRoots | (intros; apply GlobalTheory.TrEll.realTorus_norm_cxRoots <;> assumption)
end

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

theorem _root_.GlobalTheory.T.traceFormGramPowerBasis_hermitian_nondegenerate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r), IsHermND σ (GlobalTheory.TrUnitLat.gramOne P) := by
  first | exact @GlobalTheory.TrUnitLat.gramOne_herm_nd | exact GlobalTheory.TrUnitLat.gramOne_herm_nd | (intros; apply GlobalTheory.TrUnitLat.gramOne_herm_nd <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie


theorem _root_.GlobalTheory.T.relIndex_integralMatrices_cartanDouble_coset : ∀ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (m n : ℕ) (ϖ : v.adicCompletion F), IsUnifV F v ϖ → ∀ (d : Fin m → ℤ) (t : GL (Fin m) (v.adicCompletion F)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL v (n := m), ∀ k₂ ∈ KGL v (n := m), (GlobalTheory.SplitIdx.intMat F v m n).relIndex ((GlobalTheory.SplitIdx.intMat F v m n).map (GlobalTheory.SplitIdx.mulL (n := n) (k₁ * t * k₂).1)) = qV F v ^ (n * (∑ i, max (-d i) 0).toNat) := by
  first | exact @GlobalTheory.SplitIdx.LocIndex.relIndex_intMat | exact GlobalTheory.SplitIdx.LocIndex.relIndex_intMat | (intros; apply GlobalTheory.SplitIdx.LocIndex.relIndex_intMat <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie


theorem _root_.GlobalTheory.T.relIndex_movedHomLattice_eq_prod_halves_splitPlace : ∀ (D : D7) (S T : HSp D) (ε : AE D), IsSplitIdem D ε → ∀ g : GA D T, SuppAt ε T g → GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)) ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (1, g))) = (GlobalTheory.SplitIdx.halfLat S T ε).relIndex ((GlobalTheory.SplitIdx.halfLat S T ε).map (GlobalTheory.SplitIdx.actL S T g)) * (GlobalTheory.SplitIdx.halfLat S T (cA D ε)).relIndex ((GlobalTheory.SplitIdx.halfLat S T (cA D ε)).map (GlobalTheory.SplitIdx.actL S T g)) := by
  first | exact @GlobalTheory.SplitIdxDec.idx_dec | exact GlobalTheory.SplitIdxDec.idx_dec | (intros; apply GlobalTheory.SplitIdxDec.idx_dec <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ConjHol

theorem star_trace_mat_of_unitLie {D : D7} {S T : HSp D} (C : Ctx S T) {Z : Frame C.X.Ψ T.rank}
    (hZ : Z ∈ GlobalTheory.HolRead.unitLie C.X) (σ : C.X.Ψ) : star (trace (mat Z σ)) = -trace (mat Z σ) := by
  set Sg : Matrix (Fin T.rank) (Fin T.rank) ℂ := diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ) with hSg
  have hSS : Sg * Sg = 1 := by
    rw [hSg, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    unfold sgn
    split_ifs <;> norm_num
  have h := hZ σ
  have h2 : Sg * ((mat Z σ)ᴴ * Sg + Sg * mat Z σ) = 0 := by rw [h, Matrix.mul_zero]
  rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hSS, Matrix.one_mul] at h2
  have h3 := congrArg trace h2
  rw [trace_add, trace_zero, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, hSS, Matrix.mul_one,
    trace_conjTranspose] at h3
  exact eq_neg_of_add_eq_zero_left h3

theorem trace_mat_eq_zero_of_add_I {D : D7} {S T : HSp D} (C : Ctx S T) (ρ : D.what₂.Tau) (c d : Fin T.rank) (hcd : c < d)
    {Z Z' : Frame C.X.Ψ T.rank} (hZ : Z ∈ GlobalTheory.HolRead.unitLie C.X) (hZ' : Z' ∈ GlobalTheory.HolRead.unitLie C.X)
    (h : Z + I • Z' = GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) (σ : C.X.Ψ) :
    trace (mat Z σ) = 0 ∧ trace (mat Z' σ) = 0 := by
  have e : mat Z σ + I • mat Z' σ = mat (GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) σ := by rw [← h]; rfl
  have e0 : trace (mat Z σ) + I * trace (mat Z' σ) = 0 := by
    have := congrArg trace e
    rw [trace_add, trace_smul, smul_eq_mul, GlobalTheory.HolRead.AdExt.mat_unitFr] at this
    rw [this]
    split_ifs
    · simp [Matrix.trace, Matrix.single, hcd.ne']
    · simp
  have a := star_trace_mat_of_unitLie C hZ σ
  have b := star_trace_mat_of_unitLie C hZ' σ
  have e1 := congrArg star e0
  rw [star_add, star_mul', a, b, star_zero, Complex.star_def, Complex.conj_I] at e1
  have hy : trace (mat Z' σ) = 0 := by
    have : (2 * I) * trace (mat Z' σ) = 0 := by linear_combination e0 + e1
    rcases mul_eq_zero.1 this with h2 | h2
    · exfalso; simp at h2
    · exact h2
  refine ⟨?_, hy⟩
  rw [hy, mul_zero, add_zero] at e0
  exact e0

theorem trLin_toLieC_of_trace {D : D7} {S T : HSp D} (C : Ctx S T) (R : GlobalTheory.SmoothForms.RealPoints C.θ T) (B : C.Bas)
    (hB : C.IsB B) (m : D.what₂.Tau → ℤ) (W : Frame C.X.Ψ T.rank) (hW : ∀ σ, trace (mat W σ) = 0) :
    trLin T m (toLieC C R B W) = 0 := by
  change ∑ ρ, (m ρ : ℂ) * trace ((toLieC C R B W) ρ).1 = 0
  refine Finset.sum_eq_zero fun ρ _ => ?_
  change (m ρ : ℂ) * trace ((GlobalTheory.HolRead.AdExt.toLie R B (fun ρ => C.m.e ρ) (conjL W)) ρ).1 = 0
  rw [GlobalTheory.HolRead.AdExt.toLie_val, mat_conjL]
  have hN : trace ((mat W (C.m.e ρ)).map (starRingEnd ℂ)) = 0 := by
    have : trace ((mat W (C.m.e ρ)).map (starRingEnd ℂ)) = starRingEnd ℂ (trace (mat W (C.m.e ρ))) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Matrix.trace, map_sum]
    rw [this, hW, map_zero]
  set N := (mat W (C.m.e ρ)).map (starRingEnd ℂ)
  have hM : trace (B ρ * N * (B ρ)⁻¹) = 0 := by
    rw [trace_mul_cycle, nonsing_inv_mul _ (isUnit_det_B C hB ρ), Matrix.one_mul, hN]
  have hC : trace (conjAt T ρ (B ρ * N * (B ρ)⁻¹)) = 0 := by
    unfold conjAt
    rw [trace_neg, trace_mul_cycle, mul_nonsing_inv _ (R.1 ρ).2, Matrix.one_mul, trace_conjTranspose, hM, star_zero,
      neg_zero]
  rw [trace_smul, trace_add, hM, hC]
  simp

theorem trLin_toLieC_unitFr : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (R : GlobalTheory.SmoothForms.RealPoints C.θ T) (B : C.Bas), C.IsB B → ∀ (m : D.what₂.Tau → ℤ) (ρ : D.what₂.Tau) (c d : Fin T.rank), c < d → ∀ (Z Z' : Frame C.X.Ψ T.rank), Z ∈ GlobalTheory.HolRead.unitLie C.X → Z' ∈ GlobalTheory.HolRead.unitLie C.X → Z + I • Z' = GlobalTheory.HolRead.unitFr (C.m.e ρ) c d → GlobalTheory.AdSpan.ConjHol.trLin T m (GlobalTheory.AdSpan.ConjHol.toLieC C R B Z) + I * GlobalTheory.AdSpan.ConjHol.trLin T m (GlobalTheory.AdSpan.ConjHol.toLieC C R B Z') = 0 := by
  intro D S T C R B hB m ρ c d hcd Z Z' hZ hZ' h
  rw [trLin_toLieC_of_trace C R B hB m Z (fun σ => (trace_mat_eq_zero_of_add_I C ρ c d hcd hZ hZ' h σ).1),
    trLin_toLieC_of_trace C R B hB m Z' (fun σ => (trace_mat_eq_zero_of_add_I C ρ c d hcd hZ hZ' h σ).2), mul_zero, add_zero]

end GlobalTheory.AdSpan.ConjHol
end
end
