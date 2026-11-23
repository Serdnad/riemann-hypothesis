module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle020
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle014
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle031
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.EisensteinMeromorphy.Bundle001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.EisensteinMeromorphy.Bundle002
public import Development.WeilBound.ThetaLifts.LatticeBasics.EisCont
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle032
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle025
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle039
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.GIinvA
import Development.WeilBound.ThetaLifts.CartanFactorisation.Unimod
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.Bundle001
import Development.WeilBound.ThetaLifts.LatticeBasics.RatEquiv
import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle005
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.PiProdSch
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.ProdGenMem
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle034
public import Development.WeilBound.ThetaLifts.FrameEstimates.CoefEq
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle027
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitIwa
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.SiegelWeilFormula
open GlobalTheory.Cont
namespace PositivityTheory.SiegelWeilFormula.Khead
theorem eisStrong_of_k : _root_.GlobalTheory.ThK.Dbl.EisBL_k → _root_.PositivityTheory.SiegelWeilFormula.EisStrong_k := by
  intro hBL F E _ _ _ _ _ σ d hS s₁ f hf s₀
  obtain ⟨r', s', hY⟩ := hS
  obtain ⟨Ê, ⟨t, hsum, hdiff⟩, hw⟩ := hBL F E σ d.B d.n d.Y r' s' d.ok.good d.ok.hn hY d.χ d.ok.hecke d.m d.ok.res d.b d.K d.a
    d.ok.frame d.ok.stdK d.ok.hgt s₁ f hf
  have hp : ∀ s₀ : ℂ, ∃ (k : ℕ) (H : ℂ → d.G → ℂ), An.Reg (fun x : d.G => (ht2 x : ℝ)) H s₀ ∧
      ∀ᶠ s in 𝓝[≠] s₀, ∀ x, H s x = (s - s₀) ^ k * Ê s x := by
    intro s₀
    obtain ⟨k, U, H, hU, he, hd⟩ := hw s₀
    refine ⟨k, fun s => (H s).1, reg_of_weak hU hd, ?_⟩
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hU, self_mem_nhdsWithin] with s hs hne
    exact he s hs hne
  have hr : ∀ s : ℂ, t < s.re → An.Reg (fun x : d.G => (ht2 x : ℝ)) Ê s := fun s hs => by
    obtain ⟨k, H, a, e⟩ := hp s
    exact a.remove one_le_height_GL2 e ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs) hdiff
  obtain ⟨U, p, G, hUo, hUr, hs₀, hp0, hreg, heq⟩ := strip one_le_height_GL2 hp hr s₀
  obtain ⟨hGd, hGc⟩ := diff_cont_of_reg hreg
  obtain ⟨t2, hmaj⟩ := _root_.PositivityTheory.SiegelWeilFormula.Khead.majorant_k d ⟨r', s', hY⟩ hf
  have hinv := _root_.GlobalTheory.T.eisenstein_series_moderate_growth F E σ d.B d.n d.Y r' s' d.ok.good d.ok.hn hY d.b d.K d.a d.ok.frame d.ok.stdK d.ok.hgt d.χ s₁ f hf
    d.ok.hecke t Ê hsum
  have hfl : ∀ z, (fun y => ((d.Ht y : ℝ) : ℂ) ^ (z - s₁) * f y) = _root_.GlobalTheory.ThK.Dbl.flat d.a f s₁ z := fun z => funext fun y => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht, _root_.GlobalTheory.ThK.Dbl.flat]
    rw [Real.coe_toNNReal _ (hgt_nonneg d.ok.hgt y)]
  have Heisenberg₂ : ∀ z : ℂ, t < z.re → ∀ g, d.eis f s₁ z g = Ê z g := fun z hz g => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.eis]
    rw [hfl z]
    exact (hsum z hz g).tsum_eq
  refine ⟨U, p, G, max t t2, hUo, hUr, hs₀, hp0, hGd, hGc, ?_, fun z hz =>
    ⟨hmaj z (lt_of_le_of_lt (le_max_right _ _) hz), fun g => ?_⟩⟩
  · intro z hz γ hγ g
    obtain ⟨τ, hτ⟩ := hUr.1
    have han : ∀ x, AnalyticOnNhd ℂ (G · x) U := fun x => (hGd x).analyticOnNhd hUo
    have hz₀ : (((max τ t + 1 : ℝ)) : ℂ) ∈ rightOf (max τ t) := by simp
    refine (han (γ * g)).eqOn_of_preconnected_of_eventuallyEq (han g) hUr.isPreconnected
      (hτ (rightOf_subset (le_max_left _ _) hz₀)) ?_ hz
    filter_upwards [(isOpen_rightOf _).mem_nhds hz₀] with w hw
    have hw' : t < w.re := lt_of_le_of_lt (le_max_right _ _) hw
    rw [heq w hw', heq w hw', hinv w hw' γ hγ g]
  · have hz1 : t < z.re := lt_of_le_of_lt (le_max_left _ _) hz
    rw [heq z hz1, Heisenberg₂ z hz1]
end PositivityTheory.SiegelWeilFormula.Khead
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula.KSplit
namespace PositivityTheory.SiegelWeilFormula.KSplitA
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem A_sym_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∃ ε : ℤˣ, ∀ i j, σ (d.A.J j i) = ((ε : ℤ) : E) * d.A.J i j := by
  rcases d.ok.sign with ⟨h, -⟩ | ⟨h, -⟩
  · exact ⟨1, fun i j => by rw [h.herm]; simp⟩
  · exact ⟨-1, fun i j => by rw [h.skew]; simp⟩
theorem A_det_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : d.A.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have key : (d.A.J.map (d.B.emb w).1).det ≠ 0 := by
    rcases d.ok.sign with ⟨h, -⟩ | ⟨h, -⟩
    · exact det_ne_of_hasSig (h.sig w)
    · have := det_ne_of_hasSig (h.sig w)
      rw [Matrix.det_smul] at this
      exact right_ne_zero_of_mul this
  intro h0
  apply key
  rw [show d.A.J.map (d.B.emb w).1 = ((d.B.emb w).1 : E →+* ℂ).mapMatrix d.A.J from rfl, ← RingHom.map_det, h0, map_zero]
theorem mu_right_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : d.μ.IsMulRightInvariant := by
  obtain ⟨ε, hε⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSplitA.A_sym_k d
  exact (PositivityTheory.ThKF.unimodularity_holds F E σ d.cm d.m d.A.J ε hε (_root_.PositivityTheory.SiegelWeilFormula.KSplitA.A_det_k d)).2.2 d.μ d.ok.haar
theorem cw_mul'_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) {p q r : Type} [Fintype q] (A : Matrix p q (AE F E))
    (B : Matrix q r (AE F E)) : d.cw w (A * B) = d.cw w A * d.cw w B :=
  Matrix.map_mul (f := piInf (d.B.emb w))
theorem cw_sub_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) {p q : Type} (A B : Matrix p q (AE F E)) :
    d.cw w (A - B) = d.cw w A - d.cw w B := by
  ext i j
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
theorem exists_embU_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (u : Matrix (Fin d.m) (Fin d.m) ℂ)
    (hu : u ∈ Matrix.unitaryGroup (Fin d.m) ℂ) : ∃ g : UA σ d.A.J, ∀ X : Mx F E d.m d.n,
      R.loc w (mat g⁻¹ * X) = (u * Matrix.of (R.loc w X) : Matrix (Fin d.m) (Fin d.n) ℂ) ∧
        (∀ w', w' ≠ w → d.cw w' (mat g⁻¹ * X - X) = 0) ∧ finOne F • (mat g⁻¹ * X - X) = 0 := by
  set fr : Matrix (Fin d.m) (Fin d.m) ℂ := (R.fr w).1 with hfr_def
  set fri : Matrix (Fin d.m) (Fin d.m) ℂ := ((R.fr w)⁻¹).1 with hfri_def
  have hb : fr * fri = 1 := by rw [hfr_def, hfri_def, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hb' : fri * fr = 1 := by rw [hfr_def, hfri_def, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have huu : u * uᴴ = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact (Matrix.mem_unitaryGroup_iff).1 hu
  have huu' : uᴴ * u = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact (Matrix.mem_unitaryGroup_iff').1 hu
  set h : Matrix (Fin d.m) (Fin d.m) ℂ := u.map star with hh_def
  have hhs : h.map star = u := by ext i j; simp [hh_def]
  have hht : hᵀ = uᴴ := by ext i j; simp [hh_def, Matrix.conjTranspose_apply]
  have h1 : h * uᵀ = 1 := by
    have : (u * uᴴ)ᵀ = h * uᵀ := by
      rw [Matrix.transpose_mul]; congr 1
    rw [← this, huu, Matrix.transpose_one]
  have h2 : uᵀ * h = 1 := by
    have : (uᴴ * u)ᵀ = uᵀ * h := by
      rw [Matrix.transpose_mul]; congr 1
    rw [← this, huu', Matrix.transpose_one]
  set Z := fr * h * fri with hZ_def
  set Z' := fr * uᵀ * fri with hZ'_def
  have hZZ : Z * Z' = 1 := by
    rw [hZ_def, hZ'_def, show fr * h * fri * (fr * uᵀ * fri) = fr * h * (fri * fr) * uᵀ * fri by
      simp only [Matrix.mul_assoc], hb', Matrix.mul_one, Matrix.mul_assoc fr h uᵀ, h1, Matrix.mul_one, hb]
  have hZZ' : Z' * Z = 1 := by
    rw [hZ_def, hZ'_def, show fr * uᵀ * fri * (fr * h * fri) = fr * uᵀ * (fri * fr) * h * fri by
      simp only [Matrix.mul_assoc], hb', Matrix.mul_one, Matrix.mul_assoc fr uᵀ h, h2, Matrix.mul_one, hb]
  have hζ0 : R.ζ ≠ 0 := by
    rcases R.hζ with ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e]
    · exact one_ne_zero
    · exact Complex.I_ne_zero
  set D : Matrix (Fin d.m) (Fin d.m) ℂ := d.A.J.map (d.B.emb w).1 with hD_def
  set Q : Matrix (Fin d.m) (Fin d.m) ℂ := frᵀ * D * fr.map star with hQ_def
  have hQ : R.ζ • Q = ((R.sg w : ℤ) : ℂ) • 1 := R.hfr w
  have hhQ : hᵀ * Q * h.map star = Q := by
    apply smul_right_injective _ hζ0
    show R.ζ • (hᵀ * Q * h.map star) = R.ζ • Q
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hQ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hhs, hht, huu']
  have hmem : (_root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z)ᵀ * incM F d.A.J * (_root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z).map (cA σ) = incM F d.A.J := by
    refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w' => ?_) ?_
    · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Place.cw_cA_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_transpose_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k]
      unfold Krd.fam
      split_ifs with hw
      · subst hw
        exact Krd.conj_unit fr fri h D Q hb rfl hhQ
      · rw [Matrix.transpose_one, Krd.mapStar_one, Matrix.one_mul, Matrix.mul_one]
    · have e1 : (finOne F • (1 : Matrix (Fin d.m) (Fin d.m) (AE F E))).map (cA σ) = finOne F • 1 := by
        rw [Krd.map_cA_smul, Matrix.map_one _ (map_zero _) (map_one _)]
      rw [Krd.fin_mul, Krd.fin_mul, ← Matrix.transpose_smul, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k, ← Krd.map_cA_smul, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k, e1,
        Matrix.transpose_smul, Matrix.transpose_one, ← Krd.fin_mul, ← Krd.fin_mul, Matrix.mul_one, Matrix.one_mul]
  let k : UA σ d.A.J := ⟨⟨_root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z, _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z', by rw [← _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_mul_k, hZZ, _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_one_k],
    by rw [← _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_mul_k, hZZ', _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_one_k]⟩, hmem⟩
  refine ⟨k⁻¹, fun X => ⟨?_, fun w' hw' => ?_, ?_⟩⟩
  · rw [inv_inv]
    show (fri * d.cw w (_root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z * X)).map star = u * (fri * d.cw w X).map star
    rw [_root_.PositivityTheory.SiegelWeilFormula.KSplitA.cw_mul'_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k]
    simp only [Krd.fam, if_true]
    rw [hZ_def, show fri * (fr * h * fri * d.cw w X) = (fri * fr) * h * (fri * d.cw w X) by
      simp only [Matrix.mul_assoc], hb', Matrix.one_mul, mapStar_mul', hhs]
  · rw [inv_inv]
    show d.cw w' (_root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z * X - X) = 0
    rw [_root_.PositivityTheory.SiegelWeilFormula.KSplitA.cw_sub_k, _root_.PositivityTheory.SiegelWeilFormula.KSplitA.cw_mul'_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k]
    simp only [Krd.fam, if_neg hw', Matrix.one_mul, sub_self]
  · rw [inv_inv]
    show finOne F • (_root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z * X - X) = 0
    rw [smul_sub, ← Matrix.smul_mul, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k, Matrix.smul_mul, Matrix.one_mul, sub_self]
end PositivityTheory.SiegelWeilFormula.KSplitA
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Tauto
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
open PositivityTheory.ThKF0.Resc in

theorem thetaSum_rational_invariant (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (γ : d.G) (hγ : γ ∈ rat2 σ d.Y) (Ψ : d.Fn) (hΨ : Ψ ∈ d.sch) :
    thetaSum F (d.om γ Ψ) = thetaSum F Ψ := by
  have hσ : IsCMExt F E σ := d.cm
  have hψ : IsStd d.B.ψ := d.std
  have h2 : Module.finrank F E = 2 := hσ.2.2.1
  haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  obtain ⟨δ, hq⟩ := exists_isQuad hσ
  have h0 : δ ≠ 0 := hq.unit.ne_zero
  obtain ⟨-, hS, hR⟩ := d.ok.dbl.weil
  have hYd : d.Y.J.det ≠ 0 := by
    obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
    intro hz
    have hee : ((ε : ℤ) : E) * ((ε : ℤ) : E) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    have hM : (Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) *
        Matrix.fromBlocks 0 (((ε : ℤ) : E) • 1) 1 0 = 1 := by
      rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
      simp [smul_smul, hee]
    have h1 := congrArg Matrix.det hM
    rw [Matrix.det_mul, ← hε, Matrix.det_mul, Matrix.det_mul, dbl, Matrix.det_fromBlocks_zero₂₁, hz] at h1
    simp at h1
  have hκ : Fintype.card d.κ = Fintype.card (Fin d.m) * Fintype.card (Fin d.n ⊕ Fin d.n) := by
    have : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
    let bE : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E h2
    let bA := Algebra.TensorProduct.basis (AF F) bE
    haveI : Module.Free (AF F) (AE F E) := Module.Free.of_basis bA
    haveI : Module.Finite (AF F) (AE F E) := Module.Finite.of_basis bA
    have e := d.dd.e.finrank_eq
    rw [Module.finrank_matrix, Module.finrank_eq_card_basis bA, Module.finrank_prod,
      Module.finrank_fintype_fun_eq_card] at e
    simp only [Fintype.card_fin, Fintype.card_sum] at e ⊢
    omega
  obtain ⟨d₀, hd₀⟩ := exists_ratCoord h2 hκ d.dd.e d.ok.dbl.rat
  obtain ⟨a, b, hab, hA, hB⟩ : ∃ a b : E, -1 = δ * a * b ∧ IsHerm σ (a • d.A.J) ∧ IsHerm σ (b • d.Y.J) := by
    rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
    · refine ⟨1, -δ⁻¹, by field_simp, ?_, ?_⟩
      · rw [one_smul]; exact ⟨hA.herm, (herm_det hA).isUnit⟩
      · refine ⟨fun i j => by simp [hY i j, hq.anti], Ne.isUnit ?_⟩
        rw [Matrix.det_smul]
        exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero h0))) hYd
    · refine ⟨-δ⁻¹, 1, by field_simp, ?_, ?_⟩
      · refine ⟨fun i j => by simp [hA.skew i j, hq.anti], Ne.isUnit ?_⟩
        rw [Matrix.det_smul]
        exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero h0))) (skew_det hA)
      · rw [one_smul]; exact ⟨hY, hYd.isUnit⟩
  have hb : b ≠ 0 := by
    rintro rfl
    simp at hab
  have hξ : (-1 : AE F E) = inclR (F := F) (AF F) δ * inclR (F := F) (AF F) a * inclR (F := F) (AF F) b := by
    rw [← map_mul, ← map_mul, ← hab, map_neg, map_one]
  have hJA : incM F (a • d.A.J) = inclR (F := F) (AF F) a • incM F d.A.J := by
    ext i j; simp [incM]
  have hJB : incM F (dbl (b • d.Y.J)) = inclR (F := F) (AF F) b • dbl (incM F d.Y.J) := by
    ext (i | i) (j | j) <;> simp [incM, dbl]
  obtain ⟨d', om', he, hS', hR', hgg⟩ := split_resc (c := cA σ) (C := adeleClass F) (ψ := d.B.ψ) (κ := d.κ) hξ
    (hb.isUnit.map (inclR (F := F) (AF F))) hJA hJB hS.toIsSplitting hR
  have hd' : ∀ x, d'.e (incM F x) = (fun i => algebraMap F (AF F) ((d₀ x).1 i), fun i => algebraMap F (AF F) ((d₀ x).2 i)) :=
    fun x => by rw [he]; exact hd₀ x
  obtain ⟨g', hg'1, hg'2⟩ := hgg γ
  have hg : ∃ γ₀ : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E,
      ((g' : GL (Fin d.n ⊕ Fin d.n) (AE F E)) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) = incM F γ₀ := by
    obtain ⟨g₀, hg₀⟩ := Subgroup.mem_subgroupOf.mp hγ
    refine ⟨g₀, ?_⟩
    rw [hg'1, ← hg₀]
    rfl
  rw [← hg'2]
  exact split_core hψ hq (a • d.A.J) (b • d.Y.J) hA hB d' d₀ hd' d.χ d.ok.hecke om' hS' hR' g' hg Ψ hΨ
end PositivityTheory.SiegelWeilFormula.Tauto
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
theorem prodGen_mem_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (S : InfinitePlace F → 𝓢(Fin d.m → Fin d.n → ℂ, ℂ))
    (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (hg : g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F)) :
    (fun X => (∏ w, S w (R.loc w X)) * g fun k => (d.crd X k).2) ∈ d.schM := by
  obtain ⟨T, hT⟩ := piProdSch (InfinitePlace F) (Fin d.m → Fin d.n → ℂ) S
  obtain ⟨L, hL⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFock.archEquiv_k d R
  rw [_root_.PositivityTheory.SiegelWeilFormula.SD_k.schM, Submodule.mem_comap]
  refine Submodule.subset_span ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L T, g, hg, ?_⟩
  funext c
  simp only [LinearMap.funLeft_apply, pureA, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp, hT, hL,
    _root_.PositivityTheory.SiegelWeilFormula.KFock.crd_cmb_k]
theorem fock_le_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : R.fock ≤ d.schM := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨P, g, hg, rfl⟩
  have h := _root_.PositivityTheory.SiegelWeilFormula.KFock.prodGen_mem_k d R (fun w => (isSw_fP (P w)).choose) g hg
  have e : (fun X => (∏ w, fP (P w) (R.loc w X)) * g fun k => (d.crd X k).2) =
      fun X => (∏ w, (isSw_fP (P w)).choose (R.loc w X)) * g fun k => (d.crd X k).2 := by
    funext X
    congr 1
    exact Finset.prod_congr rfl fun w _ => by rw [(isSw_fP (P w)).choose_spec]
  change _ ∈ d.schM
  rw [e]
  exact h
theorem tens_mem_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (f : (Fin d.m → Fin d.n → ℂ) → ℂ) (hf : IsSw f)
    (Ψ : Mx F E d.m d.n → ℂ) (hΨ : Ψ ∈ R.away w) : R.tens w f Ψ ∈ d.schM := by
  obtain ⟨φ, hφ⟩ := hf
  have h : R.away w ≤ d.schM.comap (_root_.PositivityTheory.SiegelWeilFormula.KFock.tensL_k R w f) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨P, g, hg, rfl⟩
    have h := _root_.PositivityTheory.SiegelWeilFormula.KFock.prodGen_mem_k d R (Function.update (fun w' => (isSw_fP (P w')).choose) w φ) g hg
    show R.tens w f _ ∈ d.schM
    convert h using 1
    funext X
    show f (R.loc w X) * ((∏ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' X)) * g fun k => (d.crd X k).2) =
      (∏ w', (Function.update (fun w' => (isSw_fP (P w')).choose) w φ w') (R.loc w' X)) * g fun k => (d.crd X k).2
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w), Function.update_self, hφ, mul_assoc]
    congr 2
    refine Finset.prod_congr rfl fun w' hw' => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hw'), (isSw_fP (P w')).choose_spec]
  exact h hΨ
end PositivityTheory.SiegelWeilFormula.KFock
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Tauto
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def tr_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (g : UA σ d.A.J) (X : Matrix (Fin d.m) (Fin d.n) E) : Mx F E d.m d.n := mat g⁻¹ * incM F X
theorem cont_tr_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ d.schM) (X : Matrix (Fin d.m) (Fin d.n) E) :
    Continuous fun g : UA σ d.A.J => f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X) := by
  have h1 : Continuous (f ∘ d.cmb) := PositivityTheory.ThKEst.continuous_schA (Φ := f ∘ d.cmb) hf
  have e : ∀ Y, f Y = (f ∘ d.cmb) (d.crd Y) := fun Y => by simp [_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.cmb_crd_k]
  have h2 : Continuous fun h : UA σ d.A.J =>
      (((h : GL (Fin d.m) (AE F E))⁻¹ : GL (Fin d.m) (AE F E)) : Matrix (Fin d.m) (Fin d.m) (AE F E)) :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k, e, _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.crd_mul_k]
  exact h1.comp (((_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.continuous_mh_k d).comp h2).matrix_mulVec continuous_const)
theorem chr_comb_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (β G T : Matrix (Fin d.n) (Fin d.n) (AE F E)) :
    d.B.ψ (-(⅟(2 : AF F) * d.tt (β * G))) * d.B.ψ (-(d.tt (T * β))) =
      d.B.ψ (-(d.tt ((⅟(2 : AF F) • G + T) * β))) := by
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, add_mul, Matrix.trace_add, smul_mul_assoc, Matrix.trace_smul, map_add (f := _), map_smul, smul_eq_mul,
    Matrix.trace_mul_comm G β]
  ring
theorem half_eq_iff_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (G T : Matrix (Fin d.n) (Fin d.n) (AE F E)) :
    ⅟(2 : AF F) • G + T = 0 ↔ G = (-2 : ℤ) • T := by
  have h2 : algebraMap (AF F) (AE F E) ⅟(2 : AF F) * 2 = 1 := by
    rw [← map_ofNat (algebraMap (AF F) (AE F E)) 2, ← map_mul, invOf_mul_self, map_one]
  constructor
  · intro h
    ext i j
    have := congrFun (congrFun h i) j
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, Algebra.smul_def] at this
    rw [Matrix.smul_apply, zsmul_eq_mul]
    push_cast
    linear_combination 2 * this - G i j * h2
  · rintro rfl
    ext i j
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, Algebra.smul_def, Matrix.smul_apply, zsmul_eq_mul]
    push_cast
    linear_combination (-T i j) * h2
end PositivityTheory.SiegelWeilFormula.Tauto
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem T_zero_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Φ : d.Fn} (_hΦ : Φ ∈ d.sch) : d.T Φ 0 = d.l Φ := by
  have h0 : d.dd.rho d.B.ψ 0 Φ = Φ := by
    funext y
    simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Matrix.zero_mul, h0]
theorem gram_zero_left_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Z : Mx F E d.m d.n) : d.gram 0 Z = 0 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]
theorem cellFormula_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.CellFormula_k := by
  intro hT F E _ _ _ _ _ σ d ν hν ε w hw Φ hΦ g x β hg
  have h1 : d.sec0 Φ (w * g * x) = d.l (d.om w (d.om g (d.om x Φ))) := by
    simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.sec0, map_mul, Module.End.mul_apply]
  have hx := _root_.PositivityTheory.SiegelWeilFormula.KWhit.om_mem_sch_k d x hΦ
  have hgx := _root_.PositivityTheory.SiegelWeilFormula.KWhit.om_mem_sch_k d g hx
  rw [h1, ← _root_.PositivityTheory.SiegelWeilFormula.KWhit.T_zero_k d (_root_.PositivityTheory.SiegelWeilFormula.KWhit.om_mem_sch_k d w hgx), hT.2.2.1 F E σ d ν hν ε w hw _ hgx 0]
  refine integral_congr_ae (Filter.Eventually.of_forall fun Z => ?_)
  simp only [_root_.PositivityTheory.SiegelWeilFormula.KWhit.gram_zero_left_k, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, Matrix.trace_zero, map_zero, mul_zero, AddChar.map_zero_eq_one, one_mul]
  exact (hT.2.1 F E σ d _ hx).1 g β hg Z
end PositivityTheory.SiegelWeilFormula.KWhit
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
theorem jEx_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.JEx_k := by
  intro F E _ _ _ _ _ σ d n h Y b ε e1 e2
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (G2 σ Y) := Subgroup.instIsTopologicalGroupSubtypeMem _
  let j : G2 σ Y →* d.G := (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b).codRestrict _ (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_mem_k d h b ε e1 e2)
  have hfr : ∀ g, inFrame d.b (j g) = blk h (inFrame b g) 1 := fun g => by
    rw [inFrame_eq]
    show incM F (d.b⁻¹).1 * (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g).1 * incM F d.b.1 = _
    rw [_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_val_k]
    simp only [← Matrix.mul_assoc, incM_inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, incM_inv_mul, Matrix.mul_one]
  refine ⟨j, ?_, fun g => by rw [hfr]; exact blk_sub h _ _, fun g => by rw [hfr]; exact blk_out h _⟩
  have h1 : Continuous fun g : G2 σ Y => g.1.1 := Units.continuous_val.comp continuous_subtype_val
  have hv : Continuous fun g : G2 σ Y => (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g).1 := by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_val_k, inFrame_eq]
    exact (continuous_const.matrix_mul ((((continuous_const.matrix_mul h1).matrix_mul continuous_const).matrix_fromBlocks
      continuous_const continuous_const continuous_const).matrix_submatrix _ _)).matrix_mul continuous_const
  have hc : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h (Y := Y) b) := by
    refine Units.continuous_iff.2 ⟨hv, ?_⟩
    have e : (fun g : G2 σ Y => ((_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g)⁻¹ : GL _ _).1) = fun g : G2 σ Y => (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g⁻¹).1 :=
      funext fun g => by rw [map_inv]
    rw [e]
    exact hv.comp continuous_inv
  exact hc.subtype_mk _
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end
