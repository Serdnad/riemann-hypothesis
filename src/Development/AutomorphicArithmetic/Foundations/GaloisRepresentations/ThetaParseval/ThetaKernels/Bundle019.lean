module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.SiegelGrowthForms.IsGrowFormEvAt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle016
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle015
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle014
public import Development.WeilBound.ThetaLifts.LatticeBasics.IsCompactIntV
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
public import Development.WeilBound.ThetaLifts.FrameEstimates.CoefEq
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle011
public import Development.WeilBound.CoreStatements.LocalThetaKernels.LinearIndependentOfNotMem
public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle004
public import Development.WeilBound.ThetaLifts.FrameEstimates.SchrAddPt
public import Development.WeilBound.ThetaLifts.FrameEstimates.CoefBd
import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle005
public import Development.WeilBound.ThetaLifts.LatticeBasics.ContinuousFlat
public import Development.WeilBound.ThetaLifts.LatticeBasics.EisCont
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.EqZeroOfPiInf
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle002
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle001
import Development.WeilBound.ThetaLifts.LatticeBasics.PairsD
public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle002
public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle304

@[expose] public section

section



section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
theorem swFullX_of_k (h1 : _root_.GlobalTheory.ThK.Dbl.SWAnisoX_k) (h2 : _root_.GlobalTheory.ThK.Dbl.EisContinues_k) (h3 : _root_.GlobalTheory.ThK.Dbl.BoxSecX_k) : _root_.GlobalTheory.ThK.Dbl.SWFullX_k := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hn hd hX hW h0 hM χ hχ hr dd om S l c1 c2 K a hK ha μ D hμ hD Φ₁ p1 Φ₂ p2
  obtain ⟨U, Ê, hE, hR⟩ := h2 F E σ B n X r s hB hn (.inl hX) χ hχ d hr K a hK ha _ _
    (h3 F E σ B n d X W M r s r' s' hB hn hd hX hW h0 hM χ hχ hr dd om S l c1 c2 K a hK ha Φ₁ p1 Φ₂ p2)
  obtain ⟨k, hk⟩ := hR (((d : ℂ) - n) / 2)
  exact ⟨_, _, hE.update hk (h1 F E σ B n d X W M r s r' s' hB hn hd hX hW h0 hM χ hχ hr dd om S l c1 c2 K a hK ha μ D hμ hD Φ₁ p1 Φ₂ p2),
    Set.mem_insert _ _, fun x => by rw [Function.update_self]⟩
end GlobalTheory.ThK.Dbl
end
end
end

section



section
noncomputable section
set_option linter.unusedSectionVars false
namespace PositivityTheory.ThKEnd.Grp
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : ℕ} {J : Matrix (Fin d) (Fin d) E}
theorem level_sch_k (hL : _root_.PositivityTheory.ThKEst.Level_k) {n : ℕ} {X : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ X W} {χX χW om r s r' s'}
    (hp : _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s') {Φ : Fn F n d} (hΦ : Φ ∈ schA F _) :
    ∀ᶠ u in 𝓝 (1 : UA σ W.J), (∀ w, (mat u).map (piInf (B.emb w)) = 1) → om (1, u) Φ = Φ := by
  induction hΦ using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨U, hU, h⟩ := hL F E σ B n d X W M χX χW om r s r' s' hp g hg
    exact mem_of_superset hU fun u hu k => h u hu k f
  | zero => exact Eventually.of_forall fun _ _ => map_zero _
  | add x y _ _ hx hy => filter_upwards [hx, hy] with u h1 h2 k using by rw [map_add (f := _), h1 k, h2 k]
  | smul a x _ hx => filter_upwards [hx] with u h1 k using by rw [map_smul, h1 k]
variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {R : RealMaps F a a'}
  {Rf : FinMaps F a a'}
end PositivityTheory.ThKEnd.Grp
end
end
end

section



section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace Dense
open GlobalTheory.CompanionTheory.CMAdele
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}
end Dense
theorem polSch_k : _root_.GlobalTheory.ThK.Dbl.PolSch_k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, -, φ, h1, h2, rfl⟩
  exact Dense.pure_mem f ⟨h1, (h2.and hp.good.std).mono fun v hv => hv.1.trans hv.2⟩
end GlobalTheory.ThK.Dbl
end
end
end

section



section
noncomputable section
namespace GlobalTheory.ThK.Dbl.Prs
open scoped TensorProduct Classical
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl.Dens
open PositivityTheory.ThKF (ArchOp PureAct)
open PositivityTheory.ThK (LocRepEx)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' n d : ℕ}
  {Y : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ Y W} {o : Rep σ Y W} {R : RealMaps F a a'} {Rf : FinMaps F a a'}
  {p : SInf F (Fin n × Fin d) →ₗ[ℂ] R.Pi} {q : ∀ v, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] Rf.Pi v} {T T₁ : Finset (Pl F)}
theorem inf_op_k (hA : _root_.PositivityTheory.ThKF.ArchOp_k) {χ χ' r s r' s'} (hp : _root_.GlobalTheory.ThK.IsPair_k B M χ χ' o r s r' s') {k : UA σ W.J} (hk : k ∈ KInf σ W B.emb) :
    ∃ A : Module.End ℂ (SInf F (Fin n × Fin d)), ∀ f ∈ M.Pol B.ψ B.emb, A f ∈ M.Pol B.ψ B.emb ∧ Acts (evI F) (o (1, k)) f (A f) := by
  have o1 : (1 : UA σ Y.J) ∈ KInf σ Y B.emb :=
    ⟨fun u _ => by rw [show mat (1 : UA σ Y.J) = 1 from rfl, sub_self, smul_zero], fun w => by
      rw [show mat (1 : UA σ Y.J) = 1 from rfl, Matrix.map_one _ (map_zero _) (map_one _)]; exact Commute.one_left _⟩
  obtain ⟨A, a1, a2⟩ := hA F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hp 1 o1.1 k hk.1
  exact ⟨A, fun f hf => ⟨a2 o1 hk f hf, a1.2 f⟩⟩
variable {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
end GlobalTheory.ThK.Dbl.Prs
end
end
end

section



section
noncomputable section
namespace PositivityTheory.ThKEst
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
theorem coefEq_of_k : _root_.PositivityTheory.ThKEst.CoefEq_k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP μ hμ Φ₁ h₁ Φ₂ h₂ g h z
  have hs := IsUWeilPair.isUSplitting hP.weil
  set w := mat g⁻¹ * z * (mat h⁻¹)ᵀ with hw
  have e : actAB (cA σ) (g, h) w = z := by
    have a : mat g * mat g⁻¹ = 1 := Units.mul_inv g.1
    have b : (mat h⁻¹)ᵀ * (mat h)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, show mat h * mat h⁻¹ = 1 from Units.mul_inv h.1, Matrix.transpose_one]
    change mat g * w * (mat h)ᵀ = z
    rw [hw, Matrix.mul_assoc (mat g⁻¹), ← Matrix.mul_assoc (mat g), a, Matrix.one_mul, Matrix.mul_assoc, b,
      Matrix.mul_one]
  have i := hs.impl (g, h) w Φ₁ h₁
  rw [e] at i
  have k := inner_eq_of_unit μ (om (g, h)) (hs.pres _) (hs.unit μ hμ _)
    (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hP.base.std w Φ₁ h₁) h₂
  rw [i] at k
  exact k
end PositivityTheory.ThKEst
end
end
end

section



section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
def StdEx_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ)
    (Y : Spc F E n) r s, _root_.UpperTheory.TP.W.GoodK σ B → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∃ b K a, IsFrame2 σ Y b ∧ IsStdK (σ := σ) (Y := Y) B b K ∧ IsHgt K a ∧ Continuous a ∧ ∀ x, 0 < a x
theorem stdEx_of_k (h1 : _root_.GlobalTheory.ThK.Dbl.FrameConj_k) (h2 : _root_.GlobalTheory.ThK.Dbl.HgtEx_k) : _root_.GlobalTheory.ThK.Dbl.StdEx_k := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY
  obtain ⟨⟨K, a, hK, ha, hc, hp⟩, -⟩ := h2 F E σ B n Y r s hB hY
  obtain ⟨b, K₀, p, t, hb, hK₀, hpt, e⟩ := h1 F E σ B n Y r s hB hY K hK
  have h0 : (0 : ℝ) < absE F E (Matrix.GeneralLinearGroup.det t) := by
    rw [← ha.val p t hpt 1 K.one_mem]
    exact hp _
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalGroup (G2 σ Y) := Subgroup.instIsTopologicalGroupSubtypeMem _
  refine ⟨b, K₀, fun x => absE F E (Matrix.GeneralLinearGroup.det t) * a (x * p⁻¹), hb, hK₀, ⟨fun x => ?_, fun q u hq k hk => ?_⟩,
    continuous_const.mul (hc.comp (continuous_mul_const _)), fun x => mul_pos h0 (hp _)⟩
  · obtain ⟨q, u, hq, k, hk, ex⟩ := ha.iwa (x * p⁻¹)
    exact ⟨q * p, u * t, hq.mul hpt, _, (e k).1 hk, by rw [mul_inv_eq_iff_eq_mul.1 ex]; group⟩
  · have := ha.val _ _ (hq.mul hpt.inv) (p * k * p⁻¹) ((e _).2 (by convert hk using 1; group))
    rw [show q * k * p⁻¹ = q * p⁻¹ * (p * k * p⁻¹) by group, this, ← NNReal.coe_mul, ← map_mul, mul_comm, ← map_mul,
      inv_mul_cancel_right]
end GlobalTheory.ThK.Dbl
end
end
end

section



section
noncomputable section
namespace PositivityTheory.ThKEst
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
namespace levelStructure
open LatticeQuotientMeasure PositivityTheory.ThKF0.Grow PositivityTheory.ThKF0.Grow.Fi
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
end levelStructure
open levelStructure in
theorem level_of_k (hC : _root_.PositivityTheory.ThKEst.CoefEq_k) (hF : FourierInj) (hB : _root_.PositivityTheory.ThKEst.CoefBd_k) : _root_.PositivityTheory.ThKEst.Level_k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp φ hφ
  by_cases h0 : ∀ f : SInf F (Fin n × Fin d), pureA F f φ = 0
  · exact ⟨Set.univ, univ_mem, fun u _ _ f => by rw [h0, map_zero]⟩
  push Not at h0
  obtain ⟨f₀, h0⟩ := h0
  obtain ⟨y, hy⟩ := Function.ne_iff.1 h0
  have hy : pureA F f₀ φ y ≠ 0 := hy
  have hs := IsUWeilPair.isUSplitting hp.weil
  have mem : ∀ f : SInf F (Fin n × Fin d), pureA F f φ ∈ schA F (Fin n × Fin d) := fun f =>
    Submodule.subset_span ⟨f, φ, hφ, rfl⟩
  obtain ⟨μ, hμ, -⟩ := ParityOfCoefficients.exists_haar (F := F) (κ := Fin n × Fin d)
  obtain ⟨p, C, -, hCc, hb⟩ := hB F E σ B n d X W M χX χW om r s r' s' hp μ hμ φ hφ φ hφ 0
  have h1 := coef_near M hp.base.std hφ hCc
  have := LatticeQuotientMeasure.ring_AE F E
  have hi : Continuous fun u : UA σ W.J => u⁻¹ :=
    ((continuous_inv (G := GL (Fin d) (AE F E))).comp continuous_subtype_val).subtype_mk fun u => (u⁻¹).2
  have h2 := (hi.tendsto' 1 1 inv_one).eventually h1
  have hc : Continuous fun u : UA σ W.J => ‖om (1, u) (pureA F f₀ φ) y / pureA F f₀ φ y - 1‖ :=
    ((((hs.cont _ (ev_adm y) _ (mem f₀)).comp (continuous_const.prodMk continuous_id)).div_const _).sub
      continuous_const).norm
  have h3 := pow_near _ ((isOpen_lt hc (continuous_const (y := (1 / 2 : ℝ)))).mem_nhds (by
    change ‖om 1 (pureA F f₀ φ) y / pureA F f₀ φ y - 1‖ < 1 / 2
    rw [map_one, Module.End.one_apply, div_self hy]
    norm_num))
  refine ⟨_, h1.and (h2.and h3), fun u ⟨h1, h2, h3⟩ hu => ?_⟩
  have hu := isFin_of hp.base.cm B.emb hu
  have key : ∀ (f : SInf F (Fin n × Fin d)) x, om (1, u) (pureA F f φ) x * (starRingEnd ℂ) (om (1, u) (pureA F f₀ φ) y) =
      pureA F f φ x * (starRingEnd ℂ) (pureA F f₀ φ y) := by
    intro f x
    refine hF F _ B.ψ hp.base.std μ hμ _ (hs.pres _ _ (mem f)) _ (hs.pres _ _ (mem f₀)) _ (mem f) _ (mem f₀) ?_ x y
    funext w
    obtain ⟨z, rfl⟩ := M.co.e.surjective w
    rw [hC F E σ B n d X W M χX χW om r s r' s' hp μ hμ _ (mem f) _ (mem f₀), ParityOfCoefficients.mat_one_inv, Matrix.one_mul]
    by_cases a : ∃ c ∈ C, At (evI F) (z - c)
    · unfold coef
      rw [h2 hu.inv z a]
    by_cases a' : ∃ c ∈ C, At (evI F) (z * (mat u⁻¹)ᵀ - c)
    · unfold coef
      rw [← h1 hu _ a', Matrix.mul_assoc, ← Matrix.transpose_mul, show mat u * mat u⁻¹ = 1 from Units.mul_inv u.1,
        Matrix.transpose_one, Matrix.mul_one]
    have b := hb f f₀ z
    have b' := hb f f₀ (z * (mat u⁻¹)ᵀ)
    rw [maj, if_neg a, mul_zero, norm_le_zero_iff] at b
    rw [maj, if_neg a', mul_zero, norm_le_zero_iff] at b'
    rw [b, b']
  have h4 : (starRingEnd ℂ) (om (1, u) (pureA F f₀ φ) y) ≠ 0 := fun h => by
    have := key f₀ y
    rw [h, mul_zero, eq_comm, mul_eq_zero, map_eq_zero, or_self] at this
    exact hy this
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ f : SInf F (Fin n × Fin d), om (1, u) (pureA F f φ) = c • pureA F f φ :=
    ⟨(starRingEnd ℂ) (pureA F f₀ φ y) / (starRingEnd ℂ) (om (1, u) (pureA F f₀ φ) y), fun f => funext fun x => by
      rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff h4, key, mul_comm]⟩
  have h5 : ∀ k : ℕ, om (1, u ^ k) (pureA F f₀ φ) = c ^ k • pureA F f₀ φ := fun k => by
    induction k with
    | zero => rw [pow_zero, pow_zero, one_smul]; exact congrArg (· (pureA F f₀ φ)) (map_one om)
    | succ k ih =>
      rw [pow_succ, show ((1, u ^ k * u) : UA σ X.J × UA σ W.J) = (1, u ^ k) * (1, u) from by simp, map_mul,
        Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ']
  have h6 : c = 1 := PositivityTheory.ThKH.Locrep.eq_one_of_pow_near fun k => by
    have := h3 hu k
    rwa [Set.mem_ofPred_eq, h5, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hy, mul_one] at this
  intro f
  rw [hc, h6, one_smul]
end PositivityTheory.ThKEst
end
end
end

section



section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK NumberField.mixedEmbedding
open GlobalTheory.EmbChart (atPlace atPlace_mul_right evFin_atPlace)
open scoped TensorProduct ENNReal NNReal Classical
noncomputable section
namespace PositivityTheory.ThKEst
namespace W
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
variable {E : Type} [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
end W
open W
theorem coefBd_of_k : CoefReal → _root_.PositivityTheory.ThKEst.CoefBd_k := by
  intro hR F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP μ hμ φ₁ h₁ φ₂ h₂ N
  haveI := hP.base.cm.1
  obtain ⟨p, C, K, hp, hC, hK, h⟩ := coef_split hR hP.base.std μ hμ h₁ h₂ N
  obtain ⟨L, hL, hsz⟩ := sz_le B.emb M.co.e.symm.toLinearMap
  have hLN : 0 ≤ C * L ^ N := by positivity
  refine ⟨(NNReal.mk (1 + C * L ^ N) (by positivity)) • p,
    (fun q => M.co.e.symm (spl F _ (0, q.1), spl F _ (0, q.2))) '' K, hp.const_smul _,
    hK.image ((lin_cont M.co.e.symm.toLinearMap).comp ((spl_cont.comp (continuous_const.prodMk continuous_fst)).prodMk
      (spl_cont.comp (continuous_const.prodMk continuous_snd)))), fun f₁ f₂ z => ?_⟩
  obtain ⟨w, rfl⟩ := M.co.e.symm.surjective z
  obtain ⟨x, hx⟩ := (spl F _).surjective w.1
  obtain ⟨y, hy⟩ := (spl F _).surjective w.2
  obtain rfl : w = (spl F _ x, spl F _ y) := Prod.ext hx.symm hy.symm
  rw [LinearEquiv.apply_symm_apply]
  obtain ⟨a, b⟩ := h f₁ f₂ x y
  by_cases h0 : coef F B.ψ μ (pureA F f₁ φ₁) (pureA F f₂ φ₂) (spl F _ x, spl F _ y) = 0
  · rw [h0, norm_zero]
    exact mul_nonneg (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)) (LatticeQuotientCompactness.maj_nonneg _ _ _ _)
  have s0 := LatticeQuotientCompactness.sz_nonneg B.emb (M.co.e.symm (spl F _ x, spl F _ y))
  rw [maj, if_pos, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  · have q := mul_nonneg (apply_nonneg p f₁) (apply_nonneg p f₂)
    calc _ ≤ _ * (L * (1 + ‖x.1‖ + ‖y.1‖)) ^ N := by gcongr; exact hsz x y
      _ = L ^ N * (_ * (1 + ‖x.1‖ + ‖y.1‖) ^ N) := by rw [mul_pow, mul_left_comm]
      _ ≤ L ^ N * (C * (p f₁ * p f₂)) := by gcongr
      _ ≤ ((1 + C * L ^ N) * p f₁) * ((1 + C * L ^ N) * p f₂) := by
        nlinarith [mul_nonneg hLN q, mul_nonneg (mul_nonneg hLN hLN) q]
  · refine ⟨_, ⟨_, b h0, rfl⟩, fun u hu => ?_⟩
    rw [← map_sub, ← map_smul, map_eq_zero_iff _ M.co.e.symm.injective, Prod.mk_sub_mk, ← map_sub, ← map_sub]
    have : ∀ x : (Fin n × Fin d → mixedSpace F) × (Fin n × Fin d → Af F), u • spl F _ (x - (0, x.2)) = 0 := fun x =>
      funext fun i => by
        show u * (re F _ + fi F (x.2 i - x.2 i)) = 0
        rw [sub_self, map_zero, add_zero, ← re_add_fi u, hu, map_zero, zero_add, mul_comm, re_mul_fi]
    exact Prod.ext (this x) (this y)
end PositivityTheory.ThKEst
end
end
end

section



section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
theorem eisContinues_of_k (h1 : _root_.GlobalTheory.ThK.Dbl.EisBL_k) (h2 : _root_.GlobalTheory.ThK.Dbl.FrameConj_k) : _root_.GlobalTheory.ThK.Dbl.EisContinues_k := by
  intro F E _ _ _ _ _ σ B n Y r s hB hn hY χ hχ c hc K a hK ha s₁ f hf
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  obtain ⟨b, K₀, p, t, hb, hK₀, hp, hk⟩ := h2 F E σ B n Y r s hB hY K hK
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = absE F E (Matrix.GeneralLinearGroup.det t) := ⟨_, rfl⟩
  have d0 : 0 < d := hd ▸ absE_pos _
  have a0 : ∀ x, 0 < a x := fun x => by
    obtain ⟨q, u, hq, k, hk, rfl⟩ := ha.iwa x
    exact ha.val q u hq k hk ▸ absE_pos _
  have hk' : ∀ k ∈ K₀, p * k * p⁻¹ ∈ K := fun k h => (hk _).2 (by simpa [mul_assoc] using h)
  have ha₀ : IsHgt K₀ fun x => d * a (x * p⁻¹) := by
    refine ⟨fun x => ?_, fun q u hq k h => ?_⟩
    · obtain ⟨q, u, hq, k, h, e⟩ := ha.iwa (x * p⁻¹)
      exact ⟨q * p, _, hq.mul hp, _, (hk k).1 h, by rw [mul_inv_eq_iff_eq_mul.1 e]; group⟩
    · rw [show q * k * p⁻¹ = q * p⁻¹ * (p * k * p⁻¹) by group, ha.val _ _ (hq.mul hp.inv) _ (hk' k h), map_mul, map_mul, map_inv,
        map_inv, NNReal.coe_mul, NNReal.coe_inv, ← hd]
      field_simp
  have hf₀ : IsSec K₀ χ s₁ fun x => f (x * p⁻¹) := by
    refine ⟨hf.cont.comp (continuous_mul_const _), fun q u x hq => by rw [mul_assoc, hf.law q u _ hq], ?_⟩
    haveI := hf.fin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k : K => fun x => f (x * k.1))).map
      (LinearMap.funLeft ℂ ℂ fun x => x * p⁻¹)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨⟨_, hk' k k.2⟩, rfl⟩, funext fun x => by simp [LinearMap.funLeft, mul_assoc]⟩
  obtain ⟨Ê, ⟨t₁, e1, e2⟩, e3⟩ := h1 F E σ B n Y r s hB hn hY χ hχ c hc b K₀ _ hb hK₀ ha₀ s₁ _ hf₀
  have dc : Differentiable ℂ fun z : ℂ => (d : ℂ) ^ (s₁ - z) :=
    (differentiable_id.const_sub s₁).const_cpow (.inl (Complex.ofReal_ne_zero.2 d0.ne'))
  refine (eisCont_of_reg (f := flat a f s₁) (Ê := fun z x => (d : ℂ) ^ (s₁ - z) * Ê z (x * p)) (t := t₁) (fun z hz x => ?_)
    (fun x => dc.differentiableOn.mul (e2 _)) fun s₀ => ?_).imp fun U hU => ⟨_, hU⟩
  · refine (congrArg (HasSum · _) (funext fun q => ?_)).mp ((e1 z hz (x * p)).mul_left ((d : ℂ) ^ (s₁ - z)))
    simp only [eisTerm, flat, ← mul_assoc, mul_inv_cancel_right]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg d0.le (a0 _).le, ← mul_assoc,
      ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 d0.ne')]
    simp
  · obtain ⟨k, U, H, hU, e4, e5⟩ := e3 s₀
    refine ⟨k, _, (reg_of_weak hU e5).mul one_le_height_GL2 (dc.analyticAt s₀) (continuous_mul_const p) (b := ht2 p) fun x => ?_, ?_⟩
    · rw [mul_comm]; exact_mod_cast heightGL_mul_le F x.1 p.1
    · filter_upwards [mem_nhdsWithin_of_mem_nhds hU, self_mem_nhdsWithin] with z hz hz' x
      rw [e4 z hz hz', mul_left_comm]
end GlobalTheory.ThK.Dbl
end
end
end

section



section
noncomputable section
namespace SiegelEisensteinSeries.BRoad
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
theorem eisBL_of_k (hH : _root_.SiegelEisensteinSeries.EisHalf_k) (hM : _root_.SiegelEisensteinSeries.BRoad.SiegelMult_k) (hF : OneVarFactor) : _root_.GlobalTheory.ThK.Dbl.EisBL_k := by
  intro F E _ _ _ _ _ σ B n Y r s hB hn hY χ hχ c hc b K a hb hK ha s₁ f hf
  obtain ⟨t₀, v, hv, hvh⟩ := hH F E σ B n Y r s hB hn hY χ hχ c hc b K a hb hK ha s₁ f hf
  obtain ⟨A, H, t₁, hA, hAne, hHh, hHs⟩ := hM F E σ B n Y r s hB hn hY χ hχ c hc b K a hb hK ha s₁ f hf
  have hHv : ∀ s' : ℂ, max t₀ t₁ < s'.re → ∀ x, (H s').1 x = A s' * (v s').1 x := by
    intro s' hs' x
    have h1 := hHs s' (lt_of_le_of_lt (le_max_right _ _) hs') x
    have h2 := (hv s' (lt_of_le_of_lt (le_max_left _ _) hs') x).mul_left (A s')
    exact h1.unique h2
  let Ehat : ℂ → G2 σ Y → ℂ := fun s' x => if max t₀ t₁ < s'.re then (v s').1 x else (H s').1 x / A s'
  refine ⟨Ehat, ⟨max t₀ t₁, ?_, ?_⟩, ?_⟩
  · intro s' hs' x
    simp only [Ehat, if_pos hs']
    exact hv s' (lt_of_le_of_lt (le_max_left _ _) hs') x
  · intro x
    have hd : DifferentiableOn ℂ (fun s' => evAt x (v s')) {s' : ℂ | t₀ < s'.re} :=
      hvh (evAt x) (isGrowForm_evAt x)
    have hd' : DifferentiableOn ℂ (fun s' => (v s').1 x) {s' : ℂ | max t₀ t₁ < s'.re} :=
      (hd.mono fun s' (hs' : max t₀ t₁ < s'.re) => (show t₀ < s'.re from lt_of_le_of_lt (le_max_left _ _) hs'))
    refine hd'.congr fun s' hs' => ?_
    simp only [Ehat, if_pos (show max t₀ t₁ < s'.re from hs')]
  · intro s₀
    obtain ⟨k, U, u, hUo, hs₀U, hud, hUA⟩ := hF A hA hAne s₀
    refine ⟨k, U, fun s' => (u s')⁻¹ • H s', hUo.mem_nhds hs₀U, ?_, ?_⟩
    · intro s' hs' hne x
      obtain ⟨hu, hAs⟩ := hUA s' hs'
      have hpow : (s' - s₀) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hne)
      show (u s')⁻¹ * (H s').1 x = (s' - s₀) ^ k * Ehat s' x
      by_cases hre : max t₀ t₁ < s'.re
      · simp only [Ehat, if_pos hre]
        rw [hHv s' hre x, hAs]
        field_simp
      · simp only [Ehat, if_neg hre]
        rw [hAs]
        field_simp
    · intro μ hμ
      have h1 : DifferentiableOn ℂ (fun s' => (u s')⁻¹) U := hud.inv fun s' hs' => (hUA s' hs').1
      have h2 : DifferentiableOn ℂ (fun s' => μ (H s')) U := (hHh μ hμ).differentiableOn
      refine (h1.mul h2).congr fun s' _ => ?_
      simp [map_smul, smul_eq_mul]
end SiegelEisensteinSeries.BRoad
end
end
end
