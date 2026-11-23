module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.ArchimedeanJacquetFirstTerm.ArchimedeanWhittakerTrace.LZfcCore
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.CommuteOfUnitaryConjugate
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Em0Injective
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.UnitaryConjIff
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.RelReal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle020
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle007
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.Bundle001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCoefficientsSeparatingCharactersEqZero
import Development.WeilBound.ThetaLifts.LatticeBasics.ExistsIsGauss
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
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.WhitKOfSteps
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.SiegelWeilFormula
namespace PositivityTheory.SiegelWeilFormula.Khead
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem secK_k : _root_.PositivityTheory.SiegelWeilFormula.SecK_k := by
  intro F E _ _ _ _ _ σ d Φ hΦ
  obtain ⟨c1, c2⟩ := sec_cont_law d.ok.dbl hΦ.1
  refine ⟨c1, fun p t x hp => ?_, ?_⟩
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.sec0, s0]
    exact c2 p t x hp
  · have := hΦ.2
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k : d.K => d.om k.1 Φ)).map
      (LinearMap.pi fun x => d.l ∘ₗ d.om x)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, funext fun x => by simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.sec0, map_mul]⟩
end PositivityTheory.SiegelWeilFormula.Khead
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def IsLevi_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : d.G) : Prop :=
  ∃ t u : GL (Fin d.n) (AE F E), inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1
def IsPureT_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (Φ : d.Fn) : Prop :=
  ∃ (P : InfinitePlace F → PX d.m d.n)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.m × Fin d.n × Fin 2 → v.adicCompletion F) → ℂ),
    (∀ v, IsLocallyConstant (g v) ∧ HasCompactSupport (g v)) ∧
    (∀ᶠ v in cofinite, g v = Set.indicator {c | ∀ k, c k ∈ v.adicCompletionIntegers F} 1) ∧
    d.T Φ = fun X => (∏ w, fP (P w) (R.loc w X)) *
      ∏ᶠ v, g v (fun k => HeckeCharacterZeroLocus.SiegelWeilU.evalV F v (d.crd X k).2)
def PureSpan_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.FockMem_k → _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ Φ, d.KFin Φ → d.T Φ ∈ R.fock →
    ∃ (k : ℕ) (c : Fin k → ℂ) (Φs : Fin k → d.Fn), (∀ i, d.KFin (Φs i) ∧ _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsPureT_k R (Φs i)) ∧ Φ = ∑ i, c i • Φs i
def CellFormula_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.TAll_k → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) ν, d.IsCov ν → ∀ ε w, d.IsW ε w → ∀ Φ ∈ d.sch, ∀ (g x : d.G) (β : Mx F E d.n d.n),
    inFrame d.b g = Matrix.fromBlocks 1 β 0 1 →
      d.sec0 Φ (w * g * x) = ∫ Z, d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram Z Z))) * d.T (d.om x Φ) Z ∂ν
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.ThetaDictR
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem eps_of_form_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (hcm : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) (s : E)
    (hY : ∀ i j, σ (d.Y.J j i) = s * d.Y.J i j) : s * ((R.ε : ℤ) : E) = 1 := by
  have hσ := sig_invol hcm
  set i0 : Fin d.n := ⟨0, d.ok.hn⟩
  have key := conj_form hσ (GlobalTheory.WeilM.dbl d.Y.J) d.b.1 s (dbl_conj d.Y.J s hY) (Sum.inr i0) (Sum.inl i0)
  rw [R.hε] at key
  simpa using key.symm
theorem zeta_of_eps_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) :
    (((R.ε : ℤ) : E) = -1 → R.ζ = 1) ∧ (((R.ε : ℤ) : E) = 1 → R.ζ = Complex.I) := by
  have h2 : (1 : E) ≠ -1 := by
    intro h
    have : (2 : E) = 0 := by linear_combination h
    exact two_ne_zero this
  constructor
  · intro h
    rcases R.hζ with ⟨_, hz⟩ | ⟨he, _⟩
    · exact hz
    · rw [he] at h; exact absurd (by simpa using h) h2
  · intro h
    rcases R.hζ with ⟨he, _⟩ | ⟨_, hz⟩
    · rw [he] at h; exact absurd (by simpa using h.symm) h2
    · exact hz
theorem exists_J_ne_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∃ i j, d.A.J i j ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hJ : d.A.J = 0 := Matrix.ext hcon
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hm := d.ok.hm
  have fin : ∀ (A : Matrix (Fin d.m) (Fin d.r ⊕ Fin d.s) ℂ),
      d.r + d.s = d.m → Aᵀ * (0 : Matrix (Fin d.m) (Fin d.m) ℂ) * A.map star = Matrix.fromBlocks 1 0 0 (-1) → False := by
    intro A hrs hA
    rw [Matrix.mul_zero, Matrix.zero_mul] at hA
    rcases Nat.eq_zero_or_pos d.r with hr | hr
    · have hs : 0 < d.s := by omega
      have := congrFun (congrFun hA (Sum.inr ⟨0, hs⟩)) (Sum.inr ⟨0, hs⟩)
      simp at this
    · have := congrFun (congrFun hA (Sum.inl ⟨0, hr⟩)) (Sum.inl ⟨0, hr⟩)
      simp at this
  rcases d.ok.sign with ⟨hA, _⟩ | ⟨hA, _⟩
  · obtain ⟨hrs, A, hA'⟩ := hA.sig (InfinitePlace.mk (φ.comp (algebraMap F E)))
    rw [hJ] at hA'
    exact fin A hrs (by simpa using hA')
  · obtain ⟨hrs, A, hA'⟩ := hA.sig (InfinitePlace.mk (φ.comp (algebraMap F E)))
    rw [hJ] at hA'
    exact fin A hrs (by simpa using hA')
theorem not_herm_skew_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (hA : d.A.IsHerm σ d.B d.r d.s) (hA' : d.A.IsSkew σ d.B d.r d.s) : False := by
  obtain ⟨i, j, hij⟩ := _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.exists_J_ne_k d
  have h1 := hA.herm i j
  have h2 := hA'.skew i j
  rw [h1] at h2
  have : (2 : E) * d.A.J i j = 0 := by linear_combination h2
  rcases mul_eq_zero.1 this with h | h
  · exact two_ne_zero h
  · exact hij h
theorem zeta_of_sign'_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) :
    (d.A.IsHerm σ d.B d.r d.s → R.ζ = 1) ∧ (d.A.IsSkew σ d.B d.r d.s → R.ζ = Complex.I) := by
  have hcm := d.ok.good.cm
  constructor
  · intro hA
    rcases d.ok.sign with ⟨_, hY⟩ | ⟨hA', _⟩
    · refine (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.zeta_of_eps_k R).1 ?_
      have := _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.eps_of_form_k R hcm (-1) (fun i j => by rw [hY]; ring)
      linear_combination -this
    · exact (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.not_herm_skew_k d hA hA').elim
  · intro hA
    rcases d.ok.sign with ⟨hA', _⟩ | ⟨_, hY⟩
    · exact (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.not_herm_skew_k d hA' hA).elim
    · refine (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.zeta_of_eps_k R).2 ?_
      have := _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.eps_of_form_k R hcm 1 (fun i j => by rw [hY]; ring)
      linear_combination this
theorem eta_zeta'_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {η : E} (hη : η ≠ 0) (herm : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) :
    (σ η = η ∧ R.ζ = 1) ∨ (σ η = -η ∧ R.ζ = Complex.I) := by
  obtain ⟨i, j, hij⟩ := _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.exists_J_ne_k d
  rcases d.ok.sign with ⟨hA, _⟩ | ⟨hA, _⟩
  · left
    refine ⟨?_, (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.zeta_of_sign'_k R).1 hA⟩
    have h := herm i j
    rw [map_mul, hA.herm] at h
    exact mul_right_cancel₀ hij h
  · right
    refine ⟨?_, (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.zeta_of_sign'_k R).2 hA⟩
    have h := herm i j
    rw [map_mul, hA.skew] at h
    have : (σ η + η) * d.A.J i j = 0 := by linear_combination -h
    rcases mul_eq_zero.1 this with h' | h'
    · linear_combination h'
    · exact (hij h').elim
end PositivityTheory.SiegelWeilFormula.ThetaDictR
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl PositivityTheory.SiegelWeilFormula
namespace PositivityTheory.FTA.ZFC
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
variable {Y : Spc F E n}
theorem chr_ker_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {b : GL (Fin n ⊕ Fin n) E} (hb : IsFrame2 σ Y b)
    (β : nA σ Y b) : (∀ T : nF σ Y b, chr B.ψ b T β = 1) ↔ β ∈ nF σ Y b := by
  have hσ : ∀ a, σ (σ a) = a := GlobalTheory.LeviLine.sigma_invol hB.cm
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hB.cm.2.2.1]; norm_num)
  obtain ⟨ε, hε⟩ := hb.1
  have hβ : β.1 ∈ PositivityTheory.SiegelWeilFormula.kfour.nCond σ n ε := (PositivityTheory.SiegelWeilFormula.kfour.mem_nA_iff hσ hε β.1).1 β.2
  constructor
  · intro h
    refine (PositivityTheory.SiegelWeilFormula.kfour.mem_nF_iff β).2 (rat_of_ker hB.cm hB.std ε β.1 ?_ fun T hT => ?_)
    · have e := hβ
      simp only [PositivityTheory.SiegelWeilFormula.kfour.nCond, AddSubgroup.mem_mk, ] at e
      rw [e, Int.cast_smul_eq_zsmul]
    · have hm : incM F T ∈ nA σ Y b := by
        refine (PositivityTheory.SiegelWeilFormula.kfour.mem_nA_iff hσ hε _).2 ?_
        show (incM F T)ᵀ = -((((ε : ℤ) : AE F E)) • (incM F T).map (cA σ))
        rw [Int.cast_smul_eq_zsmul, ← incM_map_cA]
        ext i j
        have := congrFun (congrFun hT i) j
        simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply] at this ⊢
        simp only [incM, Matrix.map_apply, this, map_neg, map_zsmul]
      have hT' : (⟨incM F T, hm⟩ : nA σ Y b) ∈ nF σ Y b := (PositivityTheory.SiegelWeilFormula.kfour.mem_nF_iff _).2 ⟨T, rfl⟩
      exact h ⟨⟨incM F T, hm⟩, hT'⟩
  · intro hβF T
    obtain ⟨T₀, hT₀⟩ := (PositivityTheory.SiegelWeilFormula.kfour.mem_nF_iff β).1 hβF
    obtain ⟨T₁, hT₁⟩ := (PositivityTheory.SiegelWeilFormula.kfour.mem_nF_iff T.1).1 T.2
    unfold chr
    rw [hT₀, hT₁, ← incM_mul, trace_incM_rat, ← map_neg]
    exact hB.std.2.1 _
theorem fc_inj_pt_per_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (b : GL (Fin n ⊕ Fin n) E) (nb : nA σ Y b → G2 σ Y)
    (lam : Measure (nA σ Y b)) (𝓖 : Set (nA σ Y b)) (hb : IsFrame2 σ Y b) (hc : CoefData (σ := σ) (Y := Y) b nb lam 𝓖)
    (f : G2 σ Y → ℂ) (hf : Continuous f) (hper : ∀ β ∈ nF σ Y b, ∀ g, f (nb β * g) = f g) (x : G2 σ Y)
    (hx : ∀ T : nF σ Y b, fc B.ψ b nb lam 𝓖 f T x = 0) : f x = 0 := by
  obtain ⟨hnb, hlam, hFD, -⟩ := hc
  have hσ : ∀ a, σ (σ a) = a := GlobalTheory.LeviLine.sigma_invol hB.cm
  obtain ⟨i1, i2, i3, i4⟩ := PositivityTheory.SiegelWeilFormula.kfour.nA_top hσ hb
  obtain ⟨K, hK, hcov⟩ := PositivityTheory.SiegelWeilFormula.kfour.nF_cocompact hσ hb
  have hψ := GlobalTheory.StdCharFromIsStd.isCharAF hB.std
  have htr : Continuous (Algebra.trace (AF F) (AE F E)) := IsModuleTopology.continuous_of_linearMap _
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (nA σ Y b) (nF σ Y b) K hK hcov
    (nF σ Y b) (chr B.ψ b)
    (fun T => hψ.1.comp (htr.comp ((continuous_const.matrix_mul continuous_subtype_val).matrix_trace)).neg)
    (fun T β β' => by
      unfold chr
      rw [AddSubgroup.coe_add, Matrix.mul_add, Matrix.trace_add, map_add (f := _), neg_add, AddChar.map_add_eq_mul])
    (fun T T' β => by
      unfold chr
      rw [AddSubgroup.coe_add, AddSubgroup.coe_add, Matrix.add_mul, Matrix.trace_add, map_add (f := _), neg_add,
        AddChar.map_add_eq_mul])
    (fun β => by
      unfold chr
      rw [ZeroMemClass.coe_zero, ZeroMemClass.coe_zero, Matrix.zero_mul, Matrix.trace_zero, map_zero, neg_zero,
        AddChar.map_zero_eq_one])
    (fun T β => hψ.2.1 _)
    (_root_.PositivityTheory.FTA.ZFC.chr_ker_k hB hb)
    lam 𝓖 hlam hFD (fun β => f (nb β * x))
    (hf.comp ((PositivityTheory.SiegelWeilFormula.kfour.nb_continuous hσ hb hnb).mul continuous_const))
    (fun γ hγ β => by
      show f (nb (γ + β) * x) = f (nb β * x)
      rw [PositivityTheory.SiegelWeilFormula.kfour.nb_add hnb, mul_assoc]
      exact hper γ hγ _)
    (fun T => (integral_congr_ae (.of_forall fun β => mul_comm _ _)).trans (hx T))
  have h0 := congrFun key 0
  simpa [PositivityTheory.SiegelWeilFormula.kfour.nb_zero hnb] using h0
end PositivityTheory.FTA.ZFC
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
def thB_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ) (w : InfinitePlace F) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) ℂ :=
  d.b.1.map (d.B.emb w).1 * (jE d.n ε)ᵀ * (d.b⁻¹).1.map (d.B.emb w).1
def thA_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) : Matrix (Fin d.m) (Fin d.m) ℂ :=
  (-(Complex.I * ((((R.ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ)) * R.ζ))) • 1
theorem commute_thB_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {k : d.G} (hk : k ∈ d.K) (w : InfinitePlace F) :
    Commute ((mat2 k).map (piInf (d.B.emb w))) (_root_.PositivityTheory.SiegelWeilFormula.KK.thB_k d R.ε w) := by
  have h := d.ok.good.cm
  have e1 : d.b.1.map (d.B.emb w).1 * (d.b⁻¹).1.map (d.B.emb w).1 = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have e2 : (d.b⁻¹).1.map (d.B.emb w).1 * d.b.1.map (d.B.emb w).1 = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have hMk : (inFrame d.b k).map (piInf (d.B.emb w)) =
      (d.b⁻¹).1.map (d.B.emb w).1 * (mat2 k).map (piInf (d.B.emb w)) * d.b.1.map (d.B.emb w).1 := by
    rw [inFrame, Matrix.map_mul, Matrix.map_mul, map_incM', map_incM']
  have hu := ((d.ok.stdK k).1 hk).1 w
  have cst : ∀ x : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E, (x.map σ).map (d.B.emb w).1 =
      (x.map (d.B.emb w).1).map star := fun x => by
    ext i j; exact h.2.2.2 (d.B.emb w).1 (x i j)
  have cstA : ∀ x : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E),
      (x.map (cA σ)).map (piInf (d.B.emb w)) = (x.map (piInf (d.B.emb w))).map star :=
    fun x => by ext i j; exact GlobalTheory.ThK.Dbl.Dense.piInf_cA h (d.B.emb w) (x i j)
  have hDw : (dbl (incM F d.Y.J)).map (piInf (d.B.emb w)) = (dbl d.Y.J).map (d.B.emb w).1 := by
    rw [← map_incM']
    congr 1
    ext (i | i) (j | j) <;> simp [dbl, incM, Matrix.fromBlocks]
  have hJ : (d.b.1.map (d.B.emb w).1)ᵀ * (dbl (incM F d.Y.J)).map (piInf (d.B.emb w)) *
      (d.b.1.map (d.B.emb w).1).map star = jE d.n R.ε := by
    have := congrArg (fun x => x.map (d.B.emb w).1) R.hε
    simp only [Matrix.map_mul, Matrix.transpose_map, cst] at this
    rw [hDw, this]
    ext (i | i) (j | j) <;> by_cases hij : i = j <;> simp [jE, Matrix.fromBlocks, Matrix.smul_apply, Matrix.one_apply, hij]
  have hk2 : ((mat2 k).map (piInf (d.B.emb w)))ᵀ * (dbl (incM F d.Y.J)).map (piInf (d.B.emb w)) *
      ((mat2 k).map (piInf (d.B.emb w))).map star = (dbl (incM F d.Y.J)).map (piInf (d.B.emb w)) := by
    have hk0 : (k.1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))ᵀ * dbl (incM F d.Y.J) *
        (k.1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)).map (cA σ) = dbl (incM F d.Y.J) := k.2
    have := congrArg (fun x => x.map (piInf (d.B.emb w))) hk0
    simp only [Matrix.map_mul, Matrix.transpose_map, cstA] at this
    exact this
  exact commute_of_unitary_conjugate e1 e2 hMk hu hJ hk2
end PositivityTheory.SiegelWeilFormula.KK
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def SignOK_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {n : ℕ} (Y : Spc F E n) : Prop :=
  d.A.IsHerm σ d.B d.r d.s ∧ (∀ i j, σ (Y.J j i) = -Y.J i j) ∨ d.A.IsSkew σ d.B d.r d.s ∧ ∀ i j, σ (Y.J j i) = Y.J i j
def IsJ_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) (j : G2 σ Y →* d.G) : Prop :=
  Continuous j ∧
  (∀ g, (inFrame d.b (j g)).submatrix (Sum.map (em0 h) (em0 h)) (Sum.map (em0 h) (em0 h)) = inFrame b g) ∧
  ∀ g, ∀ u ∈ ({Sum.inl (i0 h), Sum.inr (i0 h)} : Set (Fin d.n ⊕ Fin d.n)), ∀ v,
    inFrame d.b (j g) u v = (1 : Matrix _ _ (AE F E)) u v ∧ inFrame d.b (j g) v u = (1 : Matrix _ _ (AE F E)) v u
def Res_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) (j : G2 σ Y →* d.G) {κ : Type}
    [Fintype κ] (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F Y.J))) κ)
    (om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ)) (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ Φ ∈ d.sch, ∀ Φ' ∈ schA F κ,
    (∀ X : Mx F E d.m d.n, (∀ a, X a (i0 h) = 0) → Tof d.B.ψ dd l b Φ' (X.submatrix id (em0 h)) = d.T Φ X) →
    ∀ g (X : Mx F E d.m d.n), (∀ a, X a (i0 h) = 0) → Tof d.B.ψ dd l b (om g Φ') (X.submatrix id (em0 h)) = d.T (d.om (j g) Φ) X
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def jHom_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) :
    G2 σ Y →* GL (Fin d.n ⊕ Fin d.n) (AE F E) :=
  (MulAut.conj (bA d.b)).toMonoidHom.comp ((blkGL h).comp
    ((MulAut.conj (bA (F := F) b)⁻¹).toMonoidHom.comp (UG (cA σ) (dbl (incM F Y.J))).subtype))
theorem jHom_val_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) (g : G2 σ Y) :
    (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g).1 = incM F d.b.1 * blk h (inFrame b g) 1 * incM F (d.b⁻¹).1 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.coe_subtype,
    Units.val_mul, bA_val, bA_inv_val, blkGL, Units.coe_map, blkHom, MonoidHom.coe_mk, OneHom.coe_mk, inFrame_eq]
theorem jHom_mem_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ)
    (e1 : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε) (e2 : b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε) (g : G2 σ Y) :
    _root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g ∈ UG (cA σ) (dbl (incM F d.Y.J)) := by
  have hG1 : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ).toRingHom = incM F (jeps d.n ε) := by
    rw [← e1, ← incM_gram, incM_dbl]; rfl
  have hG2 : (incM F b.1)ᵀ * dbl (incM F Y.J) * (incM F b.1).map (cA σ).toRingHom = incM F (jeps n ε) := by
    rw [← e2, ← incM_gram, incM_dbl]; rfl
  have hg : (g.1.1)ᵀ * dbl (incM F Y.J) * (g.1.1).map (cA σ).toRingHom = dbl (incM F Y.J) := g.2
  have hM := (unitary_conj_iff (cA σ).toRingHom _ _ _ _ g.1.1 (incM_mul_inv b) (incM_inv_mul b) hG2).1 hg
  rw [← inFrame_eq] at hM
  show (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g).1ᵀ * dbl (incM F d.Y.J) * (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g).1.map (cA σ).toRingHom = dbl (incM F d.Y.J)
  rw [unitary_conj_iff (cA σ).toRingHom _ _ _ _ _ (incM_mul_inv d.b) (incM_inv_mul d.b) hG1, _root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_val_k]
  have eQP : incM F (d.b⁻¹).1 * (incM F d.b.1 * blk h (inFrame b g) 1 * incM F (d.b⁻¹).1) * incM F d.b.1 =
      blk h (inFrame b g) 1 := by
    simp only [← Matrix.mul_assoc, incM_inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, incM_inv_mul, Matrix.mul_one]
  rw [eQP, incM_jeps, jepsR_blk h, ← incM_jeps, ← incM_jeps, blk_transpose, blk_map _ _ _ _ (map_zero _), blk_mul,
    blk_mul, hM]
  congr 1
  simp [Matrix.map_one _ (map_zero _) (map_one _)]
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.ThetaDictR
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem isCharAF_of_good_k (B : Base F E) (hB : _root_.UpperTheory.TP.W.GoodK σ B) : HeckeCharacterZeroLocus.SiegelWeilU.IsCharAF F B.ψ :=
  GlobalTheory.StdCharFromIsStd.isCharAF hB.std
theorem frW_det_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {η : E} (hη : η ≠ 0) (w : InfinitePlace F) :
    IsUnit (cW d.B η w • (R.fr w).1.map star).det := by
  rw [isUnit_iff_ne_zero, Matrix.det_smul]
  refine mul_ne_zero (pow_ne_zero _ (cW_ne d.B hη w)) ?_
  have hu : IsUnit (R.fr w).1.det := (Matrix.isUnit_iff_isUnit_det _).1 (R.fr w).isUnit
  have e : ((R.fr w).1.map star).det = star (R.fr w).1.det := by
    rw [← Matrix.det_conjTranspose, ← Matrix.det_transpose ((R.fr w).1)ᴴ]; rfl
  rw [e, star_ne_zero]
  exact hu.ne_zero
def frW_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (η : E) (hη : η ≠ 0) (w : InfinitePlace F) : GL (Fin d.m) ℂ :=
  Matrix.nonsingInvUnit (cW d.B η w • (R.fr w).1.map star) (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.frW_det_k R hη w)
theorem frW_frc_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (η : E) (hη : η ≠ 0) (w : InfinitePlace F) :
    (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.frW_k R η hη w).1 = cW d.B η w • (R.fr w).1.map star := rfl
theorem gW_det_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (u : GL (Fin d.n) (AE F E)) {η : E} (hη : η ≠ 0) (w : InfinitePlace F) :
    IsUnit (cW d.B η w • (((d.cw w u.1)ᵀ).map star)⁻¹).det := by
  rw [isUnit_iff_ne_zero, Matrix.det_smul]
  refine mul_ne_zero (pow_ne_zero _ (cW_ne d.B hη w)) ?_
  have hu : IsUnit u.1.det := (Matrix.isUnit_iff_isUnit_det _).1 u.isUnit
  have h1 : (d.cw w u.1).det = piInf (d.B.emb w) u.1.det := by
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw; rw [RingHom.map_det]; rfl
  have h2 : (((d.cw w u.1)ᵀ).map star).det = star (d.cw w u.1).det := by
    rw [← Matrix.det_conjTranspose]; rfl
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', h2, h1]
  exact inv_ne_zero (star_ne_zero.2 (hu.map (piInf (d.B.emb w))).ne_zero)
def gW_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (u : GL (Fin d.n) (AE F E)) (η : E) (hη : η ≠ 0) (w : InfinitePlace F) : GL (Fin d.n) ℂ :=
  Matrix.nonsingInvUnit (cW d.B η w • (((d.cw w u.1)ᵀ).map star)⁻¹) (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.gW_det_k d u hη w)
theorem gW_gc_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (u : GL (Fin d.n) (AE F E)) (η : E) (hη : η ≠ 0) (w : InfinitePlace F) :
    (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.gW_k d u η hη w).1 * ((d.cw w u.1)ᵀ).map star = cW d.B η w • 1 := by
  have hu : IsUnit u.1.det := (Matrix.isUnit_iff_isUnit_det _).1 u.isUnit
  have hN : IsUnit (((d.cw w u.1)ᵀ).map star).det := by
    have h1 : (d.cw w u.1).det = piInf (d.B.emb w) u.1.det := by
      unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw; rw [RingHom.map_det]; rfl
    have h2 : (((d.cw w u.1)ᵀ).map star).det = star (d.cw w u.1).det := by
      rw [← Matrix.det_conjTranspose]; rfl
    rw [h2, h1, isUnit_iff_ne_zero, star_ne_zero]
    exact (hu.map (piInf (d.B.emb w))).ne_zero
  change (cW d.B η w • (((d.cw w u.1)ᵀ).map star)⁻¹) * ((d.cw w u.1)ᵀ).map star = cW d.B η w • 1
  rw [Matrix.smul_mul, Matrix.nonsing_inv_mul _ hN]
def εsW_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (η : E) (w : InfinitePlace F) (_ : Fin d.m) : Bool :=
  decide (0 < (((d.B.emb w).1 η / R.ζ) * ((R.sg w : ℤ) : ℂ)).re)
end PositivityTheory.SiegelWeilFormula.ThetaDictR
end
end
end
