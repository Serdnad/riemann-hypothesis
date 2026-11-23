module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle020
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle007
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.Bundle003
import Development.WeilBound.ThetaLifts.SmallCones.Bundle001
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
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle019
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle011

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl SiegelEisensteinSeries.Grp
namespace PositivityTheory.SiegelWeilFormula.kfour
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
theorem sigma_sigma_of_good_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (a : E) : σ (σ a) = a := by
  obtain ⟨-, -, -, h⟩ := hB.cm
  let τ : E →+* ℂ := Classical.arbitrary _
  apply τ.injective
  rw [h, h, star_star]
theorem coefData_exists_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {b : GL (Fin n ⊕ Fin n) E} (hb : IsFrame2 σ Y b) :
    ∃ nb lam 𝓖, CoefData (σ := σ) (Y := Y) b nb lam 𝓖 := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k hB
  obtain ⟨hlc, hsc, ht2, hbo⟩ := nA_top hσ hb
  obtain ⟨K, hK, hc⟩ := nF_cocompact hσ hb
  obtain ⟨lam, 𝓖, hlam, h𝓖, h1⟩ :=
    (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (nA σ Y b) (nF σ Y b) K hK hc).1
  exact ⟨nbE σ Y b, lam, 𝓖, isNMap_nbE hσ hb, hlam, h𝓖, h1⟩
theorem coefEx_k : _root_.PositivityTheory.SiegelWeilFormula.CoefEx_k := fun _F _E _ _ _ _ _ _σ d => _root_.PositivityTheory.SiegelWeilFormula.kfour.coefData_exists_k d.ok.good d.ok.frame
end PositivityTheory.SiegelWeilFormula.kfour
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFock
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section Cmb
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem cmb_add_k (c c' : Fin d.m × Fin d.n × Fin 2 → AF F) : d.cmb (c + c') = d.cmb c + d.cmb c' := by
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb, Pi.add_apply, Matrix.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib]
theorem cmb_eq_k (c : Fin d.m × Fin d.n × Fin 2 → AF F) (i : Fin d.m) (j : Fin d.n) :
    d.cmb c i j = ∑ k, c (i, j, k) • Algebra.TensorProduct.basis (AF F) d.bs k := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
theorem crd_cmb'_k (c : Fin d.m × Fin d.n × Fin 2 → AF F) : d.crd (d.cmb c) = c := by
  funext k
  obtain ⟨i, j, l⟩ := k
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, _root_.PositivityTheory.SiegelWeilFormula.KFock.cmb_eq_k]
  exact congrFun ((Algebra.TensorProduct.basis (AF F) d.bs).repr_sum_self fun k => c (i, j, k)) l
theorem cmb_crd_k (X : Mx F E d.m d.n) : d.cmb (d.crd X) = X := by
  ext i j
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.cmb_eq_k]
  exact (Algebra.TensorProduct.basis (AF F) d.bs).sum_repr (X i j)
theorem continuous_cmb_k : Continuous d.cmb := by
  obtain ⟨i1, -, -, -⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [_root_.PositivityTheory.SiegelWeilFormula.KFock.cmb_eq_k]
  exact continuous_finsetSum _ fun k _ => ((continuous_apply (i, j, k)).smul continuous_const)
theorem continuous_crd_k : Continuous d.crd := by
  obtain ⟨i1, -, -, -⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  refine continuous_pi fun k => ?_
  have hl : Continuous (((Finsupp.lapply k.2.2).comp (Algebra.TensorProduct.basis (AF F) d.bs).repr.toLinearMap :
      AE F E →ₗ[AF F] AF F)) := IsModuleTopology.continuous_of_linearMap _
  exact hl.comp ((continuous_apply k.2.1).comp (continuous_apply k.1))
def cmbE_k : (Fin d.m × Fin d.n × Fin 2 → AF F) ≃ₜ+ Mx F E d.m d.n where
  toFun := d.cmb
  invFun := d.crd
  left_inv := _root_.PositivityTheory.SiegelWeilFormula.KFock.crd_cmb'_k d
  right_inv := _root_.PositivityTheory.SiegelWeilFormula.KFock.cmb_crd_k d
  map_add' := _root_.PositivityTheory.SiegelWeilFormula.KFock.cmb_add_k d
  continuous_toFun := _root_.PositivityTheory.SiegelWeilFormula.KFock.continuous_cmb_k d
  continuous_invFun := _root_.PositivityTheory.SiegelWeilFormula.KFock.continuous_crd_k d
end Cmb
theorem int_schM_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ν : Measure (Mx F E d.m d.n)) (hν : ν.IsAddHaarMeasure) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ d.schM) : Integrable f ν := by
  obtain ⟨i1, i2, i3, i4⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) := inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : BorelSpace (Fin d.m × Fin d.n × Fin 2 → AF F) := Pi.borelSpace
  let e : (Fin d.m × Fin d.n × Fin 2 → AF F) ≃ᵐ Mx F E d.m d.n := (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmbE_k d).toHomeomorph.toMeasurableEquiv
  haveI : (Measure.map e.symm ν).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmbE_k d).symm
  have h1 : Integrable (f ∘ e) (Measure.map e.symm ν) := by
    have hf' : f ∘ d.cmb ∈ schA F (Fin d.m × Fin d.n × Fin 2) := Submodule.mem_comap.mp hf
    refine intSchA _ ?_ _ inferInstance hf'
    exact congrArg (fun m => @MeasurableSpace.pi (Fin d.m × Fin d.n × Fin 2) (fun _ => AF F) fun _ => m) measAF_eq
  have h2 := (integrable_map_equiv e f).2 h1
  rwa [MeasurableEquiv.map_map_symm] at h2
end PositivityTheory.SiegelWeilFormula.KFock
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.tweyl
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem std_k : IsStd d.B.ψ := d.ok.good.std
include d in
theorem cm_k : IsCMExt F E σ := d.ok.good.1
theorem hS_k : IsUSplitting (adeleClass F) d.B.ψ d.dd (fun (g : UA σ d.A.J) x => mat g * x) d.S := d.ok.dbl.lin
theorem hO_k : IsUSplitting (adeleClass F) d.B.ψ d.dd (actB (cA σ)) d.om := d.ok.dbl.weil.2.1
theorem hR_k : SiegelRule (cA σ) (adeleClass F) d.B.ψ (-1) (incM F d.A.J) (dbl (incM F d.Y.J)) d.dd d.χ
    (diagCols (Fin d.n)) d.om := d.ok.dbl.weil.2.2
theorem mat_mul_inv_k (g : UA σ d.A.J) : mat g * mat g⁻¹ = 1 := by
  show g.1.1 * (g⁻¹).1.1 = 1
  rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
end PositivityTheory.SiegelWeilFormula.tweyl
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Kdil
open PositivityTheory.Rg.Sw.Glob (aC ptZ jC gC actZ jF IsSiegel gZf)
open Matrix
variable {n : ℕ}
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem abs_tw_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) : |2 * Real.pi * ((R.sg w : ℤ) : ℝ)| = 2 * Real.pi := by
  rcases Int.units_eq_one_or (R.sg w) with h | h <;> simp [h, abs_of_pos Real.pi_pos]
end PositivityTheory.SiegelWeilFormula.Kdil
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def SD_k.Indep (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ) : Prop :=
  ∀ X Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → Ψ (X + Z) = Ψ X
def AdDecomp_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ ε w, d.IsW ε w → ∀ (e : AF F), e * e = e → ∀ x : d.G,
  e • inFrame d.b x = e • (1 : Matrix _ _ (AE F E)) →
  ∃ (x₁ x₂ x₃ x₄ : d.G) (t c b : Mx F E d.n d.n) (a a' : GL (Fin d.n) (AE F E)), x = x₁ * (w * x₂ * w⁻¹) * x₃ * x₄ ∧
    inFrame d.b x₁ = Matrix.fromBlocks 1 t 0 1 ∧ inFrame d.b x₂ = Matrix.fromBlocks 1 c 0 1 ∧
    inFrame d.b x₃ = Matrix.fromBlocks a.1 0 0 a'.1 ∧ inFrame d.b x₄ = Matrix.fromBlocks 1 b 0 1 ∧
    e • t = 0 ∧ e • c = 0 ∧ e • b = 0 ∧ e • a.1 = e • (1 : Mx F E d.n d.n) ∧ e • a'.1 = e • (1 : Mx F E d.n d.n)
def AwayAct_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ w (x : d.G), d.cw w (inFrame d.b x) = 1 →
  ∃ A : (Mx F E d.m d.n → ℂ) → Mx F E d.m d.n → ℂ, ∀ Ψ, d.Indep w Ψ → d.Indep w (A Ψ) ∧
    ∀ f, IsSw f → ∀ Φ ∈ d.sch, d.T Φ = R.tens w f Ψ → d.T (d.om x Φ) = R.tens w f (A Ψ)
def FinAct_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ x : d.G, (∀ w, d.cw w (inFrame d.b x) = 1) →
  ∀ g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F), ∃ g' ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F),
    ∀ f : Mx F E d.m d.n → ℂ, (∀ X Z, (∀ w, d.cw w Z = 0) → f (X + Z) = f X) → ∀ Φ ∈ d.sch,
      d.T Φ = (fun X => f X * g fun k => (d.crd X k).2) → d.T (d.om x Φ) = fun X => f X * g' fun k => (d.crd X k).2
end PositivityTheory.SiegelWeilFormula
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem exists_poly_k {Φ : d.Fn} (hΦ : d.KFin Φ) {k : d.G} (hk : k ∈ d.K) :
    ∃ q : Polynomial ℂ, q ≠ 0 ∧ ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • d.om (k ^ i) Φ = 0 := by
  set V := Submodule.span ℂ (Set.range fun k : d.K => d.om k.1 Φ) with hV
  have : FiniteDimensional ℂ V := hΦ.2
  have hmap : ∀ v ∈ V, d.om k v ∈ V := by
    intro v hv
    refine Submodule.span_induction (p := fun v _ => d.om k v ∈ V) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨k', rfl⟩
      refine Submodule.subset_span ⟨⟨k * k'.1, d.K.mul_mem hk k'.2⟩, ?_⟩
      simp [map_mul]
    · simp
    · intro x y _ _ hx hy; simpa using V.add_mem hx hy
    · intro a x _ hx; simpa using V.smul_mem a hx
  have hΦV : Φ ∈ V := Submodule.subset_span ⟨1, by simp⟩
  set f : V →ₗ[ℂ] V := (d.om k).restrict hmap
  have hpow : ∀ (i : ℕ) (v : V), (((f ^ i) v : V) : d.Fn) = d.om (k ^ i) v := by
    intro i
    induction i with
    | zero => intro v; simp
    | succ i ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, map_mul, Module.End.mul_apply]
      rfl
  refine ⟨minpoly ℂ f, minpoly.ne_zero (Algebra.IsIntegral.isIntegral f), ?_⟩
  have h0 := congrArg (fun g : Module.End ℂ V => ((g ⟨Φ, hΦV⟩ : V) : d.Fn)) (minpoly.aeval ℂ f)
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, Submodule.coe_sum] at h0
  simpa only [LinearMap.smul_apply, Submodule.coe_smul, hpow, LinearMap.zero_apply, ZeroMemClass.coe_zero] using h0
end PositivityTheory.SiegelWeilFormula.KFP
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
abbrev spf_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (a b : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) : AF F :=
  symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J)) a b
end PositivityTheory.SiegelWeilFormula.KFP
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
def kfS_k : Submodule ℂ d.Fn where
  carrier := {Φ | ∃ N : Submodule ℂ d.Fn, FiniteDimensional ℂ N ∧ N ≤ d.sch ∧ Φ ∈ N ∧ ∀ k ∈ d.K, ∀ Ψ ∈ N, d.om k Ψ ∈ N}
  zero_mem' := ⟨⊥, inferInstance, bot_le, zero_mem _, fun k _ g hg => by rw [(Submodule.mem_bot ℂ).1 hg, map_zero]; exact zero_mem _⟩
  add_mem' := by
    rintro f g ⟨N, _, h0, h1, h2⟩ ⟨N', _, h0', h1', h2'⟩
    refine ⟨N ⊔ N', inferInstance, sup_le h0 h0', Submodule.add_mem_sup h1 h1', fun k hk g hg => ?_⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hg
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (h2 k hk x hx) (h2' k hk y hy)
  smul_mem' := fun c _ ⟨N, h, h0, h1, h2⟩ => ⟨N, h, h0, N.smul_mem c h1, h2⟩
variable {d}
theorem kFin_of_mem_k {Φ : d.Fn} (h : Φ ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.kfS_k d) : d.KFin Φ := by
  obtain ⟨N, _, h0, h1, h2⟩ := h
  refine ⟨h0 h1, Submodule.finiteDimensional_of_le (S₂ := N) (Submodule.span_le.2 ?_)⟩
  rintro _ ⟨k, rfl⟩
  exact h2 k.1 k.2 Φ h1
theorem mem_sch_k {Φ : d.Fn} (h : Φ ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.kfS_k d) : Φ ∈ d.sch := by
  obtain ⟨N, _, h0, h1, -⟩ := h
  exact h0 h1
end PositivityTheory.SiegelWeilFormula.KK
end
end
end

section



section
noncomputable section
open scoped Matrix Classical
open NumberField MeasureTheory GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def SD_k.IsAwayW (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ) : Prop :=
  ∀ X Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → Ψ (X + Z) = Ψ X
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d)
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.GoodAway (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ) : Prop :=
  d.IsAwayW w Ψ ∧ Ψ ≠ 0 ∧ ∀ f, IsSw f → R.tens w f Ψ ∈ d.schM
end RD
def GoodAwayEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F), ∃ Ψ, R.GoodAway w Ψ
end PositivityTheory.SiegelWeilFormula
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KMain
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem rho_add_k (w) (Φ Φ' : d.Fn) : d.dd.rho d.B.ψ w (Φ + Φ') = d.dd.rho d.B.ψ w Φ + d.dd.rho d.B.ψ w Φ' := by
  funext y
  simp [Darboux.rho, schr, mul_add]
theorem rho_smul_k (w) (a : ℂ) (Φ : d.Fn) : d.dd.rho d.B.ψ w (a • Φ) = a • d.dd.rho d.B.ψ w Φ := by
  funext y
  simp [Darboux.rho, schr, mul_left_comm]
def Tl_k : d.Fn →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun := d.T
  map_add' Φ Φ' := by
    funext X
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Pi.add_apply, _root_.PositivityTheory.SiegelWeilFormula.KMain.rho_add_k, map_add (f := _)]
  map_smul' a Φ := by
    funext X
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Pi.smul_apply, _root_.PositivityTheory.SiegelWeilFormula.KMain.rho_smul_k, map_smul, RingHom.id_apply]
theorem Tl_apply_k (Φ : d.Fn) : _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_k d Φ = d.T Φ := rfl
def secl_k : d.Fn →ₗ[ℂ] (d.G → ℂ) where
  toFun := d.sec0
  map_add' Φ Φ' := by
    funext x
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.sec0, Pi.add_apply, map_add (f := _)]
  map_smul' a Φ := by
    funext x
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.sec0, Pi.smul_apply, map_smul, RingHom.id_apply]
theorem secl_apply_k (Φ : d.Fn) : _root_.PositivityTheory.SiegelWeilFormula.KMain.secl_k d Φ = d.sec0 Φ := rfl
theorem om_mem_k (x : d.G) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.om x Φ ∈ d.sch :=
  d.ok.dbl.weil.2.1.pres x Φ h
theorem S_mem_k (g) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.S g Φ ∈ d.sch :=
  d.ok.dbl.lin.pres g Φ h
theorem thetaSum_add_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) {Φ Φ' : d.Fn} (h : Φ ∈ d.sch) (h' : Φ' ∈ d.sch) :
    thetaSum F (Φ + Φ') = thetaSum F Φ + thetaSum F Φ' := by
  have h1 := (hT F E σ d Φ h).1
  have h2 := (hT F E σ d Φ' h').1
  have h3 := (hT F E σ d (Φ + Φ') (d.sch.add_mem h h')).1
  have h4 := h1.add h2
  rw [← _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k] at h3
  simp only [map_add (f := _), Pi.add_apply, _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k] at h3
  exact h3.unique h4
theorem thetaSum_smul_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (a : ℂ) {Φ : d.Fn} (h : Φ ∈ d.sch) : thetaSum F (a • Φ) = a * thetaSum F Φ := by
  have h1 := (hT F E σ d Φ h).1
  have h3 := (hT F E σ d (a • Φ) (d.sch.smul_mem a h)).1
  have h4 := h1.mul_left a
  rw [← _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k] at h3
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k] at h3
  exact h3.unique h4
theorem I_add_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.ThetaAuto_k) {Φ Φ' : d.Fn} (h : Φ ∈ d.sch) (h' : Φ' ∈ d.sch) :
    d.I (Φ + Φ') = d.I Φ + d.I Φ' := by
  funext x
  have i1 := ((hA F E σ d).2.2 Φ h).1 x
  have i2 := ((hA F E σ d).2.2 Φ' h').1 x
  have e : ∀ g, thetaSum F (d.om x (d.S g (Φ + Φ'))) = thetaSum F (d.om x (d.S g Φ)) + thetaSum F (d.om x (d.S g Φ')) :=
    fun g => by
      rw [map_add (f := _), map_add (f := _)]
      exact _root_.PositivityTheory.SiegelWeilFormula.KMain.thetaSum_add_k d hT (_root_.PositivityTheory.SiegelWeilFormula.KMain.om_mem_k d x (_root_.PositivityTheory.SiegelWeilFormula.KMain.S_mem_k d g h)) (_root_.PositivityTheory.SiegelWeilFormula.KMain.om_mem_k d x (_root_.PositivityTheory.SiegelWeilFormula.KMain.S_mem_k d g h'))
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.I, thetaMean, Pi.add_apply, e]
  rw [average_eq, average_eq, average_eq, integral_add i1 i2, smul_add]
theorem I_smul_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (a : ℂ) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.I (a • Φ) = a • d.I Φ := by
  funext x
  have e : ∀ g, thetaSum F (d.om x (d.S g (a • Φ))) = a * thetaSum F (d.om x (d.S g Φ)) :=
    fun g => by
      rw [map_smul, map_smul]
      exact _root_.PositivityTheory.SiegelWeilFormula.KMain.thetaSum_smul_k d hT a (_root_.PositivityTheory.SiegelWeilFormula.KMain.om_mem_k d x (_root_.PositivityTheory.SiegelWeilFormula.KMain.S_mem_k d g h))
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.I, thetaMean, Pi.smul_apply, e, smul_eq_mul]
  rw [average_eq, average_eq, integral_const_mul, mul_smul_comm]
theorem I_sum_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.ThetaAuto_k) {ι : Type} (s : Finset ι) (f : ι → d.Fn) (h : ∀ i ∈ s, f i ∈ d.sch) :
    d.I (∑ i ∈ s, f i) = ∑ i ∈ s, d.I (f i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have := _root_.PositivityTheory.SiegelWeilFormula.KMain.I_smul_k d hT 0 (d.sch.zero_mem)
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      _root_.PositivityTheory.SiegelWeilFormula.KMain.I_add_k d hT hA (h a (Finset.mem_insert_self _ _)) (d.sch.sum_mem fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]
end PositivityTheory.SiegelWeilFormula.KMain
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Krd
def EpsEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ),
  ∃ ε : ℤˣ, d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 ∧
    (d.A.IsHerm σ d.B d.r d.s ∧ ε = -1 ∨ d.A.IsSkew σ d.B d.r d.s ∧ ε = 1)
def FrEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ),
  (d.A.IsHerm σ d.B d.r d.s → ∃ (fr : InfinitePlace F → GL (Fin d.m) ℂ) (sg : InfinitePlace F → ℤˣ),
    ∀ w, (1 : ℂ) • ((fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (fr w).1.map star) = ((sg w : ℤ) : ℂ) • 1) ∧
  (d.A.IsSkew σ d.B d.r d.s → ∃ (fr : InfinitePlace F → GL (Fin d.m) ℂ) (sg : InfinitePlace F → ℤˣ),
    ∀ w, Complex.I • ((fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (fr w).1.map star) = ((sg w : ℤ) : ℂ) • 1)
def IotaEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ),
  ∀ (ε : ℤˣ) (ζ : ℂ), d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 →
    (ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) →
    ∃ ι : InfinitePlace F → (GR d.n →* d.G), (∀ w, Continuous (ι w)) ∧
      (∀ w y, dZ d.n ζ * d.cw w (inFrame d.b (ι w y)) = mR y * dZ d.n ζ) ∧
      (∀ w w' y, w' ≠ w → d.cw w' (inFrame d.b (ι w y)) = 1) ∧
      ∀ w y, finOne F • inFrame d.b (ι w y) = finOne F • (1 : Matrix _ _ (AE F E))
theorem rdEx_of_k (h1 : _root_.PositivityTheory.SiegelWeilFormula.Krd.EpsEx_k) (h2 : _root_.PositivityTheory.SiegelWeilFormula.Krd.FrEx_k) (h3 : _root_.PositivityTheory.SiegelWeilFormula.Krd.IotaEx_k) : _root_.PositivityTheory.SiegelWeilFormula.RDEx_k := by
  intro F E _ _ _ _ _ σ d
  obtain ⟨ε, hε, hs⟩ := h1 F E σ d
  rcases hs with ⟨hA, rfl⟩ | ⟨hA, rfl⟩
  · obtain ⟨fr, sg, hfr⟩ := (h2 F E σ d).1 hA
    obtain ⟨ι, hc, ha, ho, hf⟩ := h3 F E σ d (-1) 1 hε (Or.inl ⟨rfl, rfl⟩)
    exact ⟨⟨-1, 1, fr, sg, ι, hε, Or.inl ⟨rfl, rfl⟩, hfr, hc, ha, ho, hf⟩⟩
  · obtain ⟨fr, sg, hfr⟩ := (h2 F E σ d).2 hA
    obtain ⟨ι, hc, ha, ho, hf⟩ := h3 F E σ d 1 Complex.I hε (Or.inr ⟨rfl, rfl⟩)
    exact ⟨⟨1, Complex.I, fr, sg, ι, hε, Or.inr ⟨rfl, rfl⟩, hfr, hc, ha, ho, hf⟩⟩
end PositivityTheory.SiegelWeilFormula.Krd
end
end
end
