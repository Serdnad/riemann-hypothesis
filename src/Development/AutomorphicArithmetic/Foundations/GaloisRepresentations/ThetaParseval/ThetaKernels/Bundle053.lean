module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayFinBase
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.VolumeIsAddHaar
public import Development.WeilBound.ThetaLifts.SmallCones.Bundle001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.Bundle006
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.AwStep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle033
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle025
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle035
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle034
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle038
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle037
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.DoubledGroupTopologicalProperties

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KAway
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace SDf
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem stepN_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (x : d.G) (β : Mx F E d.n d.n) (hx : inFrame d.b x = Matrix.fromBlocks 1 β 0 1)
    (hβ : eInf F • β = 0) :
    _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d x id (fun G X => d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram X X))) * G X) := by
  have hβ' : β = finOne F • β := by
    conv_lhs => rw [← smul_split β, hβ, zero_add]
  have hβM : ∀ M : Mx F E d.n d.n, finOne F • M = 0 → β * M = 0 := fun M hM => by
    rw [hβ', Matrix.smul_mul, ← Matrix.mul_smul, hM, Matrix.mul_zero]
  refine ⟨fun f hf => hf, fun G hG => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · intro X Z hZ
    show d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram (X + Z) (X + Z)))) * G (X + Z) =
      d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram X X))) * G X
    rw [hG X Z hZ]
    have e : β * d.gram (X + Z) (X + Z) = β * d.gram X X := by
      rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_add_left_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_add_right_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_add_right_k, Matrix.mul_add, Matrix.mul_add, Matrix.mul_add,
        hβM (d.gram X Z) (by rw [← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_smul_right_k, hZ]; simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]),
        hβM (d.gram Z X) (by rw [← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_smul_left_k, hZ]; simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]),
        hβM (d.gram Z Z) (by rw [← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_smul_left_k, hZ]; simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram])]
      simp
    rw [e]
  · funext X
    rw [((hT.2.1 F E σ d) Φ hΦ).1 x β hx X, hTΦ]
    simp only [id]
    ring
theorem stepM_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (x : d.G) (a a' : GL (Fin d.n) (AE F E))
    (hx : inFrame d.b x = Matrix.fromBlocks a.1 0 0 a'.1) (ha : eInf F • a'.1 = eInf F • (1 : Mx F E d.n d.n)) :
    ∃ B, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d x id B := by
  set M : Mx F E d.n d.n := (a'⁻¹).1 with hM
  have hMe : eInf F • M = eInf F • (1 : Mx F E d.n d.n) := by
    have h1 : a'.1 * M = 1 := by rw [hM, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc eInf F • M = (eInf F • (1 : Mx F E d.n d.n)) * M := by rw [Matrix.smul_mul, Matrix.one_mul]
      _ = (eInf F • a'.1) * M := by rw [ha]
      _ = eInf F • (1 : Mx F E d.n d.n) := by rw [Matrix.smul_mul, h1]
  refine ⟨fun G X => (d.χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
      (((absE F E (Matrix.GeneralLinearGroup.det a) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) * G (X * Mᵀ),
    fun f hf => hf, fun G hG => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · intro X Z hZ
    show _ * G ((X + Z) * Mᵀ) = _ * G (X * Mᵀ)
    rw [Matrix.add_mul, hG _ _ (by rw [← Matrix.smul_mul, hZ, Matrix.zero_mul])]
  · funext X
    rw [((hT.2.1 F E σ d) Φ hΦ).2.1 x a a' hx X, hTΦ]
    have hf' : f (X * Mᵀ) = f X := by
      have e : X * Mᵀ = X + X * (M - 1)ᵀ := by
        rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.mul_one]
        abel
      rw [e]
      refine hf X _ ((_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_zero_iff_k d _).2 ?_)
      rw [← Matrix.mul_smul, Matrix.transpose_sub, smul_sub, ← Matrix.transpose_smul, ← Matrix.transpose_smul, hMe,
        sub_self, Matrix.mul_zero]
    beta_reduce
    rw [hf']
    simp only [id]
    ring
end SDf
end PositivityTheory.SiegelWeilFormula.KAway
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KAway
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace SDf
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem stepW_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (ε : ℤˣ) (w : d.G) (hw : d.IsW ε w) : ∃ A B, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d w A B := by
  obtain ⟨⟨ν, hν⟩, -, -⟩ := hA F E σ d
  have := hν.1
  obtain ⟨i1, i2, i3, i4⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) := inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))
  haveI : LocallyCompactSpace (Mx F E d.m d.n) := inferInstanceAs (LocallyCompactSpace (Fin d.m → Fin d.n → AE F E))
  haveI : SecondCountableTopology (Mx F E d.m d.n) :=
    inferInstanceAs (SecondCountableTopology (Fin d.m → Fin d.n → AE F E))
  haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))
  have hsm : ∀ c : AF F, Continuous fun Z : Mx F E d.m d.n => c • Z := fun c =>
    continuous_pi fun i => continuous_pi fun j =>
      Continuous.fun_smul (f := fun _ : Mx F E d.m d.n => c) (g := fun Z : Mx F E d.m d.n => Z i j) continuous_const
        ((continuous_apply j).comp (continuous_apply i))
  let VI : AddSubgroup (Mx F E d.m d.n) :=
    { carrier := {Z | finOne F • Z = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_add, ha, hb, add_zero]
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_neg, ha, neg_zero] }
  let VF : AddSubgroup (Mx F E d.m d.n) :=
    { carrier := {Z | eInf F • Z = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_add, ha, hb, add_zero]
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_neg, ha, neg_zero] }
  have hVI : IsClosed ((VI : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n)) :=
    isClosed_eq (hsm (finOne F)) continuous_const
  have hVF : IsClosed ((VF : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n)) :=
    isClosed_eq (hsm (eInf F)) continuous_const
  haveI : LocallyCompactSpace VI := hVI.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace VF := hVF.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology VI :=
    TopologicalSpace.Subtype.secondCountableTopology ((VI : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n))
  haveI : SecondCountableTopology VF :=
    TopologicalSpace.Subtype.secondCountableTopology ((VF : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n))
  haveI : BorelSpace VI := Subtype.borelSpace (fun x' => x' ∈ ((VI : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n)))
  haveI : BorelSpace VF := Subtype.borelSpace (fun x' => x' ∈ ((VF : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n)))
  have h₁ : ∀ Z : Mx F E d.m d.n, eInf F • Z ∈ VI := fun Z => by
    show finOne F • eInf F • Z = 0
    rw [smul_smul, finOne_mul_eInf, zero_smul]
  have h₂ : ∀ Z : Mx F E d.m d.n, finOne F • Z ∈ VF := fun Z => by
    show eInf F • finOne F • Z = 0
    rw [smul_smul, eInf_mul_finOne, zero_smul]
  let Φs : VI × VF ≃ₜ+ Mx F E d.m d.n :=
    { toFun := fun p => p.1.1 + p.2.1
      invFun := fun Z => (⟨eInf F • Z, h₁ Z⟩, ⟨finOne F • Z, h₂ Z⟩)
      left_inv := fun p => by
        obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := p
        have ha' : finOne F • a = 0 := ha
        have hb' : eInf F • b = 0 := hb
        have ea : eInf F • a = a := by
          conv_rhs => rw [← smul_split a]
          rw [ha', add_zero]
        have eb : finOne F • b = b := by
          conv_rhs => rw [← smul_split b]
          rw [hb', zero_add]
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · show eInf F • (a + b) = a
          rw [smul_add, ea, hb', add_zero]
        · show finOne F • (a + b) = b
          rw [smul_add, eb, ha', zero_add]
      right_inv := fun Z => smul_split Z
      map_add' := fun p q => by
        show p.1.1 + q.1.1 + (p.2.1 + q.2.1) = p.1.1 + p.2.1 + (q.1.1 + q.2.1)
        abel
      continuous_toFun := (continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)
      continuous_invFun := ((hsm (eInf F)).subtype_mk h₁).prodMk ((hsm (finOne F)).subtype_mk h₂) }
  obtain ⟨C, -, hC⟩ := KFock.integral_split ν (Measure.addHaar : Measure VI) (Measure.addHaar : Measure VF) Φs
  refine ⟨fun f X => (C : ℂ) * ∫ a : VI, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X a.1)) * f a.1 ∂Measure.addHaar,
    fun G X => ∫ b : VF, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X b.1)) * G b.1 ∂Measure.addHaar, fun f hf => ?_,
    fun G hG => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · intro X Z hZ
    have hZ' := (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_zero_iff_k d Z).1 hZ
    dsimp only
    congr 2
    funext a
    rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_add_left_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_fin_inf_k d hZ' a.2, add_zero]
  · intro X Z hZ
    dsimp only
    congr 1
    funext b
    rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_add_left_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_inf_fin_k d hZ b.2, add_zero]
  · funext X
    rw [(hT.2.2.1 F E σ d) ν hν ε w hw Φ hΦ X, hTΦ, hC]
    have hpt : ∀ p : VI × VF, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X (Φs p))) * (f (Φs p) * G (Φs p)) =
        (d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X p.1.1)) * f p.1.1) * (d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X p.2.1)) * G p.2.1) := by
      intro p
      have e1 : Φs p = p.1.1 + p.2.1 := rfl
      have hf' : f (p.1.1 + p.2.1) = f p.1.1 := hf p.1.1 p.2.1 ((_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_zero_iff_k d _).2 p.2.2)
      have hG' : G (p.1.1 + p.2.1) = G p.2.1 := by rw [add_comm]; exact hG p.2.1 p.1.1 p.1.2
      rw [e1, hf', hG', _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_add_right_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.tt_add_k, mul_add, AddChar.map_add_eq_mul]
      ring
    simp only [hpt]
    rw [integral_prod_mul (μ := (Measure.addHaar : Measure VI)) (ν := (Measure.addHaar : Measure VF))
      (fun a : VI => d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X a.1)) * f a.1)
      (fun b : VF => d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X b.1)) * G b.1)]
    ring
end SDf
end PositivityTheory.SiegelWeilFormula.KAway
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem j_comm_dil_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (w : InfinitePlace F) (τ : ℝ) (y : GR d.n)
    (hy : IsDil (Pi.single L.i₀ 1) τ y) (g : L.sd.G) : L.j g * R.ι w y = R.ι w y * L.j g := by
  apply PositivityTheory.SiegelWeilFormula.kfour.inFrame_injective d.b
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, _root_.PositivityTheory.SiegelWeilFormula.AStep.inFrame_dil_k R w L.i₀ τ y hy]
  ext u v
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hv : v ∈ ({Sum.inl L.i₀, Sum.inr L.i₀} : Set (Fin d.n ⊕ Fin d.n))
  · rw [((L.j_out g) v hv u).2, Matrix.one_apply]
    split_ifs with huv
    · subst huv; ring
    · simp
  · by_cases hu : u ∈ ({Sum.inl L.i₀, Sum.inr L.i₀} : Set (Fin d.n ⊕ Fin d.n))
    · rw [((L.j_out g) u hu v).1, Matrix.one_apply]
      split_ifs with huv
      · subst huv; ring
      · simp
    · rw [dilV_off d.cm w L.i₀ τ u hu, dilV_off d.cm w L.i₀ τ v hv, one_mul, mul_one]
theorem l_eq_T_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Ψ : d.Fn) (hΨ : Ψ ∈ d.sch) : d.l Ψ = d.T Ψ 0 := by
  have h1 := d.ok.dbl.kill 0 Ψ hΨ
  have h2 : ∀ M : Matrix (Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E), (0 : Matrix (Fin d.m) (Fin d.n) (AE F E)) * M = 0 :=
    fun M => Matrix.zero_mul M
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.T
  rw [← h1]
  congr 2
  ext i j
  exact (congrFun (congrFun (Matrix.zero_mul (diagCols (Fin d.n))ᵀ) i) j).trans
    (congrFun (congrFun (Matrix.zero_mul (incM F d.b.1.toCols₂)ᵀ) i) j).symm
theorem inFrame_dil'_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (i₀ : Fin d.n) (τ : ℝ) (y : GR d.n)
    (hy : IsDil (Pi.single i₀ 1) τ y) :
    inFrame d.b (R.ι w y) = Matrix.fromBlocks (dilT d.cm w i₀ τ).1 0 0 (dilT d.cm w i₀ (-τ)).1 := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.AStep.inFrame_dil_k R w i₀ τ y hy]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.diagonal_apply, dilT, dilV]
theorem constantTerm_dilation (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (i₀ : Fin d.n) (τ : ℝ) (y : GR d.n)
    (hy : IsDil (Pi.single i₀ 1) τ y) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (h : d.G) :
    d.sec0 Φ (R.ι w y * h) = Complex.exp (τ * d.m) * d.sec0 Φ h := by
  haveI := d.cm.1
  have hpres : ∀ x, ∀ Ψ ∈ d.sch, d.om x Ψ ∈ d.sch := d.ok.dbl.weil.2.1.pres
  have hΨ := hpres h Φ hΦ
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.sec0
  rw [map_mul, Module.End.mul_apply, _root_.PositivityTheory.SiegelWeilFormula.AStep.l_eq_T_k d _ (hpres _ _ hΨ), _root_.PositivityTheory.SiegelWeilFormula.AStep.l_eq_T_k d _ hΨ,
    ((H.tAll.2.1 F E σ d _ hΨ).2.1 (R.ι w y) (dilT d.cm w i₀ τ) (dilT d.cm w i₀ (-τ)) (_root_.PositivityTheory.SiegelWeilFormula.AStep.inFrame_dil'_k R w i₀ τ y hy) 0),
    det_dilT, _root_.PositivityTheory.SiegelWeilFormula.AStep.chi_adrU_k d w τ, absE_adrU d.cm w τ]
  have hz : ∀ M : Matrix (Fin d.n) (Fin d.n) (AE F E), d.T (d.om h Φ) ((0 : Mx F E d.m d.n) * M) = d.T (d.om h Φ) 0 :=
    fun M => congrArg _ (Matrix.zero_mul M)
  rw [hz, ← Real.exp_mul, Complex.ofReal_exp, one_mul]
  congr 2
  push_cast; ring
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KAway
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem cw_mul_k (w : InfinitePlace F) {p q r : Type} [Fintype q] (M : Matrix p q (AE F E)) (N : Matrix q r (AE F E)) :
    d.cw w (M * N) = d.cw w M * d.cw w N := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
  exact Matrix.map_mul
theorem cw_one_k (w : InfinitePlace F) {p : Type} [DecidableEq p] : d.cw w (1 : Matrix p p (AE F E)) = 1 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
  exact Matrix.map_one _ (map_zero _) (map_one _)
theorem cw_transpose_k (w : InfinitePlace F) {p q : Type} (M : Matrix p q (AE F E)) : d.cw w Mᵀ = (d.cw w M)ᵀ := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.transpose_map]
theorem cw_eW_self_k (w : InfinitePlace F) {p q : Type} (M : Matrix p q (AE F E)) : d.cw w (eW w • M) = d.cw w M := by
  ext i j
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, piInf_eW]
theorem cw_eW_ne_k {w w' : InfinitePlace F} (h : w' ≠ w) {p q : Type} (M : Matrix p q (AE F E)) : d.cw w' (eW w • M) = 0 := by
  ext i j
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, piInf_eW, h]
theorem eW_smul_eq_iff_k (w : InfinitePlace F) {p q : Type} (M M' : Matrix p q (AE F E)) :
    eW w • M = eW w • M' ↔ d.cw w M = d.cw w M' := by
  constructor
  · intro h
    rw [← _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eW_self_k d w M, h, _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eW_self_k]
  · intro h
    apply _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d
    · intro w'
      by_cases hw : w' = w
      · subst hw
        rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eW_self_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eW_self_k, h]
      · rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eW_ne_k d hw, _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eW_ne_k d hw]
    · rw [finOne_eW_smul, finOne_eW_smul]
theorem eW_smul_of_supp_k {w : InfinitePlace F} {p q : Type} {Z : Matrix p q (AE F E)}
    (hZ : ∀ w', w' ≠ w → d.cw w' Z = 0) (hf : finOne F • Z = 0) : eW w • Z = Z := by
  apply _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d
  · intro w'
    by_cases hw : w' = w
    · subst hw
      rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eW_self_k]
    · rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eW_ne_k d hw, hZ w' hw]
  · rw [finOne_eW_smul, hf]
theorem gram_smul_right_k (a : AF F) (X Z : Mx F E d.m d.n) : d.gram X (a • Z) = a • d.gram X Z := by
  have : (a • Z).map (cA σ) = a • Z.map (cA σ) := by
    ext i j
    simp [map_smul]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, this, Matrix.mul_smul]
theorem gram_smul_left_k (a : AF F) (X Z : Mx F E d.m d.n) : d.gram (a • X) Z = a • d.gram X Z := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, Matrix.transpose_smul, Matrix.smul_mul]
theorem gram_add_k (X Z : Mx F E d.m d.n) :
    d.gram (X + Z) (X + Z) = d.gram X X + (d.gram X Z + d.gram Z X + d.gram Z Z) := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.map_add _ (map_add _)]
  abel
theorem cw_eq_one_of_k (w : InfinitePlace F) {M : Mx F E d.n d.n} (h : eW w • M = eW w • (1 : Mx F E d.n d.n)) :
    d.cw w M = 1 := by
  rw [(_root_.PositivityTheory.SiegelWeilFormula.KAway.eW_smul_eq_iff_k d w M 1).1 h, _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_one_k]
namespace Step
variable {d} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem stepN_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (x : d.G) (β : Mx F E d.n d.n) (hx : inFrame d.b x = Matrix.fromBlocks 1 β 0 1)
    (hβ : eW w • β = 0) :
    R.StepOK w x id (fun Ψ X => d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram X X))) * Ψ X) := by
  have hP := hT.2.1 F E σ d
  refine ⟨fun f hf => hf, fun Ψ hΨ => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · intro X Z hZ hf
    have hZe : eW w • Z = Z := _root_.PositivityTheory.SiegelWeilFormula.KAway.eW_smul_of_supp_k d hZ hf
    have h1 : d.gram X Z = eW w • d.gram X Z := by
      calc d.gram X Z = d.gram X (eW w • Z) := by rw [hZe]
        _ = _ := _root_.PositivityTheory.SiegelWeilFormula.KAway.gram_smul_right_k d _ X Z
    have h2 : d.gram Z X = eW w • d.gram Z X := by
      calc d.gram Z X = d.gram (eW w • Z) X := by rw [hZe]
        _ = _ := _root_.PositivityTheory.SiegelWeilFormula.KAway.gram_smul_left_k d _ Z X
    have h3 : d.gram Z Z = eW w • d.gram Z Z := by
      calc d.gram Z Z = d.gram (eW w • Z) Z := by rw [hZe]
        _ = _ := _root_.PositivityTheory.SiegelWeilFormula.KAway.gram_smul_left_k d _ Z Z
    have key : β * d.gram (X + Z) (X + Z) = β * d.gram X X := by
      rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.gram_add_k, h1, h2, h3, ← smul_add, ← smul_add, Matrix.mul_add, Matrix.mul_smul, ← Matrix.smul_mul, hβ,
        Matrix.zero_mul, add_zero]
    simp only
    rw [key, hΨ X Z hZ hf]
  · funext X
    rw [(hP Φ hΦ).1 x β hx X, hTΦ]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, id]
    ring
theorem stepM_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (x : d.G) (a a' : GL (Fin d.n) (AE F E))
    (hx : inFrame d.b x = Matrix.fromBlocks a.1 0 0 a'.1) (ha : eW w • a'.1 = eW w • (1 : Mx F E d.n d.n)) :
    R.StepOK w x id (fun Ψ X => (d.χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
      (((absE F E (Matrix.GeneralLinearGroup.det a) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) * Ψ (X * (a'⁻¹).1ᵀ)) := by
  have hP := hT.2.1 F E σ d
  have hc : d.cw w (a'⁻¹).1 = 1 := by
    have h1 : d.cw w a'.1 = 1 := _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eq_one_of_k d w ha
    have h2 : d.cw w ((a'⁻¹).1 * a'.1) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one, _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_one_k]
    rwa [_root_.PositivityTheory.SiegelWeilFormula.KAway.cw_mul_k, h1, Matrix.mul_one] at h2
  refine ⟨fun f hf => hf, fun Ψ hΨ => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · intro X Z hZ hf
    simp only
    rw [Matrix.add_mul, hΨ (X * (a'⁻¹).1ᵀ) (Z * (a'⁻¹).1ᵀ) (fun w' hw' => by rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.cw_mul_k, hZ w' hw', Matrix.zero_mul])
      (by rw [← Matrix.smul_mul, hf, Matrix.zero_mul])]
  · funext X
    rw [(hP Φ hΦ).2.1 x a a' hx X, hTΦ]
    have hl : R.loc w (X * (a'⁻¹).1ᵀ) = R.loc w X := by
      unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc
      rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_transpose_k, hc, Matrix.transpose_one, Matrix.mul_one]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, id, hl]
    ring
end Step
end PositivityTheory.SiegelWeilFormula.KAway
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
structure Hyp_k (nb : nA σ d.Y d.b → d.G) (uM : (Fin L.n → AE F E) → d.G) (nb' : nA σ L.Y L.b → G2 σ L.Y) (w₁ : d.G)
    (cM : (Fin L.n → AE F E) × AF F → d.G) (δ : E) : Prop where
  nb : IsNMap d.b nb
  uM : ∀ u, ∃ a', inFrame d.b (uM u) = Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u) 0 0 a'
  nb' : IsNMap L.b nb'
  wr : w₁ ∈ rat2 σ d.Y
  wf : ∃ a b : E, a ≠ 0 ∧ b ≠ 0 ∧ inFrame d.b w₁ = 1 - Matrix.single (Sum.inl L.i₀) (Sum.inl L.i₀) 1 -
      Matrix.single (Sum.inr L.i₀) (Sum.inr L.i₀) 1 + Matrix.single (Sum.inl L.i₀) (Sum.inr L.i₀) (inclR (F := F) (AF F) a) +
      Matrix.single (Sum.inr L.i₀) (Sum.inl L.i₀) (inclR (F := F) (AF F) b)
  cf : ∀ c, ∃ A', inFrame d.b (cM c) = Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ c.2) 0 A'
  δ0 : δ ≠ 0
def sM_k (b : Fin L.n → AE F E) : d.G := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.elt_k (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.bMat_k (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L b))
def pb_k (β : nA σ d.Y d.b) : Fin L.n → AE F E := fun j => β.1 L.i₀ (L.em j)
def pa_k (δ : E) (β : nA σ d.Y d.b) : AF F := ellA δ (β.1 L.i₀ L.i₀)
def eisensteinSecondTerm (Φ : d.G → ℂ) (g : d.G) : ℂ := ∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, Φ (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1 * g)
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
end
