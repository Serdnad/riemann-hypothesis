module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle007
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HintConstMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1237
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle576
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1680
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle602
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle550
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle587
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
import GroundTheory.LocalFields.PadicLogSeries
public import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.SectionTrace.SecOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.SymIdx
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.PeakCone
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle004
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle001
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA GlobalTheory.CompanionTheory.ActTr
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.FactorAction

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def fHm (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) : Hf E a b →* H E a b :=
  (finGL E a).prodMap (finGL E b)

def epsS {S : Set (Pl E)} (a b : ℕ) : ∀ i : Slot S, GLw a i.pl × GLw b i.pl →* Hf E a b
  | .inl w => (locGL E a w.1).prodMap (locGL E b w.1)
  | .inr w => ((thF E a).comp (locGL E a w.1)).prodMap ((thF E b).comp (locGL E b w.1))

def selS {S : Set (Pl E)} (φ₁ φ₂ : ∀ w : Pl E, LF a b w) : ∀ i : Slot S, LF a b i.pl
  | .inl w => φ₁ w.1
  | .inr w => φ₂ w.1

theorem continuous_thF (n : ℕ) : Continuous (thF E n) :=
  GlobalTheory.ThetaPull.continuous_thetaGL _ (continuous_conjFin _)

theorem continuous_loc (n : ℕ) (w : Pl E) : Continuous (locGL E n w) :=
  GlobalTheory.EulerTw.continuous_locGL_spl E n w

theorem continuous_epsS {S : Set (Pl E)} (i : Slot S) : Continuous (epsS a b i) := by
  rcases i with w | w
  · exact (continuous_loc a w.1).prodMap (continuous_loc b w.1)
  · exact ((continuous_thF a).comp (continuous_loc a w.1)).prodMap ((continuous_thF b).comp (continuous_loc b w.1))

theorem embT_prod (w : Pl E) : (embT a w).prodMap (embT b w) =
    (fHm E a b).comp (((thF E a).comp (locGL E a w)).prodMap ((thF E b).comp (locGL E b w))) := by
  refine MonoidHom.ext fun m => Prod.ext ?_ ?_
  · exact GlobalTheory.ThetaPull.thetaA_finGL _
  · exact GlobalTheory.ThetaPull.thetaA_finGL _

theorem actS_eq {S : Set (Pl E)} (φ₁ φ₂ : ∀ w : Pl E, LF a b w) (i : Slot S) (G : H E a b → ℂ) :
    actS φ₁ φ₂ i G = act ((fHm E a b).comp (epsS a b i)) (K2 a b i.pl) (selS φ₁ φ₂ i) G := by
  rcases i with w | w
  · rfl
  · show act ((embT a w.1).prodMap (embT b w.1)) (K2 a b w.1) (φ₂ w.1) G = _
    rw [embT_prod]
    rfl

theorem pair_maximal_compact_open_compact (w : Pl E) : IsCompact (K2 a b w : Set (GLw a w × GLw b w)) ∧ IsOpen (K2 a b w : Set (GLw a w × GLw b w)) :=
  ⟨(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2,
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1⟩

theorem hecke_of_test {φ : ∀ w : Pl E, LF a b w} (h : IsTestP φ) (w : Pl E) :
    ∃ A : Subgroup (GLw a w × GLw b w), IsOpen (A : Set (GLw a w × GLw b w)) ∧ IsHecke A (φ w) := by
  obtain ⟨K₁, K₂, h₁, h₂, h₃⟩ := h
  exact ⟨(K₁ w).prod (K₂ w), (h₁.1 w).1.prod (h₂.1 w).1, h₃.1 w⟩

theorem hecke_sel {S : Set (Pl E)} {φ₁ φ₂ : ∀ w : Pl E, LF a b w} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂) (i : Slot S) :
    ∃ A : Subgroup (GLw a i.pl × GLw b i.pl), IsOpen (A : Set (GLw a i.pl × GLw b i.pl)) ∧ IsHecke A (selS φ₁ φ₂ i) := by
  rcases i with w | w
  · exact hecke_of_test h₁ w.1
  · exact hecke_of_test h₂ w.1

theorem locGL_comm {n : ℕ} {w w' : Pl E} (h : w ≠ w') (g : GLw n w) (g' : GLw n w') :
    locGL E n w g * locGL E n w' g' = locGL E n w' g' * locGL E n w g := by
  have key : ∀ v, GeneralLinearGroup.map (pLoc E v) (locGL E n w g * locGL E n w' g') =
      GeneralLinearGroup.map (pLoc E v) (locGL E n w' g' * locGL E n w g) := fun v => by
    rw [map_mul, map_mul]
    by_cases hv : v = w
    · subst hv
      rw [pLoc_locGL_of_ne h g', mul_one, one_mul]
    · rw [pLoc_locGL_of_ne hv g, mul_one, one_mul]
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun v => ?_)
  exact congrArg (fun u : GL (Fin n) (v.adicCompletion E) => u.val i j) (key v)

theorem thF_loc {n : ℕ} {w u : Pl E} (h : w = GlobalTheory.ThetaSatake.cw u) (g : GLw n w) :
    ∃ g₀ : GLw n u, thF E n (locGL E n w g) = locGL E n u g₀ := by
  subst h
  exact ⟨_, GlobalTheory.ThetaSatake.theta_locGL u g⟩

theorem cw_cw (w : Pl E) : w = GlobalTheory.ThetaSatake.cw (GlobalTheory.ThetaSatake.cw w) :=
  (GlobalTheory.ThetaPull.conjSrc_conjSrc w).symm

theorem comm_WT {n : ℕ} {w w' : Pl E} (h : w ≠ GlobalTheory.ThetaSatake.cw w') (g : GLw n w) (g' : GLw n w') :
    locGL E n w g * thF E n (locGL E n w' g') = thF E n (locGL E n w' g') * locGL E n w g := by
  obtain ⟨g₀, e⟩ := thF_loc (cw_cw w') g'
  rw [e]
  exact locGL_comm h g g₀

theorem comm_TT {n : ℕ} {w w' : Pl E} (h : GlobalTheory.ThetaSatake.cw w ≠ GlobalTheory.ThetaSatake.cw w') (g : GLw n w) (g' : GLw n w') :
    thF E n (locGL E n w g) * thF E n (locGL E n w' g') = thF E n (locGL E n w' g') * thF E n (locGL E n w g) := by
  obtain ⟨g₀, e⟩ := thF_loc (cw_cw w) g
  obtain ⟨g₁, e'⟩ := thF_loc (cw_cw w') g'
  rw [e, e']
  exact locGL_comm h g₀ g₁

theorem epsS_comm {S : Set (Pl E)} (hS : IsSection S) {i j : Slot S} (hij : i ≠ j)
    (x : GLw a i.pl × GLw b i.pl) (y : GLw a j.pl × GLw b j.pl) :
    epsS a b i x * epsS a b j y = epsS a b j y * epsS a b i x := by
  rcases i with w | w <;> rcases j with w' | w'
  · have hne : w.1 ≠ w'.1 := fun e => hij (congrArg Sum.inl (Subtype.ext e))
    exact Prod.ext (locGL_comm hne _ _) (locGL_comm hne _ _)
  · have hne : w.1 ≠ GlobalTheory.ThetaSatake.cw w'.1 := fun e =>
      GlobalTheory.CompanionTheory.SuppFinTw.conj_not_mem hS w'.2.1 w'.2.2 (show GlobalTheory.ThetaSatake.cw w'.1 ∈ S from e ▸ w.2)
    exact Prod.ext (comm_WT hne _ _) (comm_WT hne _ _)
  · have hne : w'.1 ≠ GlobalTheory.ThetaSatake.cw w.1 := fun e =>
      GlobalTheory.CompanionTheory.SuppFinTw.conj_not_mem hS w.2.1 w.2.2 (show GlobalTheory.ThetaSatake.cw w.1 ∈ S from e ▸ w'.2)
    exact Prod.ext (comm_WT hne _ _).symm (comm_WT hne _ _).symm
  · have hne : GlobalTheory.ThetaSatake.cw w.1 ≠ GlobalTheory.ThetaSatake.cw w'.1 := fun e =>
      hij (congrArg Sum.inr (Subtype.ext ((cw_cw w.1).trans ((congrArg GlobalTheory.ThetaSatake.cw e).trans (cw_cw w'.1).symm))))
    exact Prod.ext (comm_TT hne _ _) (comm_TT hne _ _)

theorem selS_conv {S : Set (Pl E)} (φ₁ φ₂ ψ₁ ψ₂ : ∀ w : Pl E, LF a b w) (i : Slot S) :
    selS (fun w => PositivityTheory.Rg.BcN.F2.mconv (φ₁ w) (ψ₁ w)) (fun w => PositivityTheory.Rg.BcN.F2.mconv (φ₂ w) (ψ₂ w)) i =
      fun m => hint (K2 a b i.pl) fun m' => selS φ₁ φ₂ i m' * selS ψ₁ ψ₂ i (m'⁻¹ * m) := by
  rcases i with w | w <;> rfl

theorem actAlg : ActAlg := by
  intro E _ _ _ a b S hS φ₁ φ₂ ψ₁ ψ₂ hφ₁ hφ₂ hψ₁ hψ₂ G G' hG hG' i j
  have hGl : Lev (fHm E a b) G := hG
  have hGl' : Lev (fHm E a b) G' := hG'
  obtain ⟨hK, hKo⟩ := pair_maximal_compact_open_compact (a := a) (b := b) i.pl
  obtain ⟨hKj, hKoj⟩ := pair_maximal_compact_open_compact (a := a) (b := b) j.pl
  obtain ⟨A, hA, hf⟩ := hecke_sel (S := S) hφ₁ hφ₂ i
  obtain ⟨B, hB, hg⟩ := hecke_sel (S := S) hψ₁ hψ₂ i
  obtain ⟨B', hB', hg'⟩ := hecke_sel (S := S) hψ₁ hψ₂ j
  have ci := continuous_epsS (a := a) (b := b) i
  have cj := continuous_epsS (a := a) (b := b) j
  refine ⟨?_, fun c => ?_, fun hij => ?_, ?_⟩
  · rw [actS_eq]
    exact act_lev ci hK hKo hA hf hGl
  · simp only [actS_eq]
    exact act_add hK hKo hA hf (sm_of_lev ci hGl) (sm_of_lev ci hGl') c
  · simp only [actS_eq]
    refine act_comm hK hKo hA hKj hKoj hB' hf hg' (sm_of_lev ci hGl) (sm_of_lev cj hGl) fun x y => ?_
    simp only [MonoidHom.comp_apply]
    rw [← map_mul, ← map_mul, epsS_comm hS hij]
  · simp only [actS_eq]
    rw [selS_conv]
    exact act_conv hK hKo hA hB hf hg (sm_of_lev ci hGl)

end GlobalTheory.CompanionTheory.FactorAction

end
end

section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtHecke

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isUnifV_of_ordL {w : Pl E} {x : w.adicCompletion E} (h0 : x ≠ 0) (h : ordL x = 1) : IsUnifV E w x := by
  have hv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  unfold ordL at h
  rw [dite_eq_right hv] at h
  have e : WithZero.unzero hv = Multiplicative.ofAdd (-1 : ℤ) := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd]
    omega
  unfold IsUnifV
  rw [← e, WithZero.coe_unzero]

theorem ordL_eq_zero {w : Pl E} {x : w.adicCompletion E} (h : Valued.v x = 1) : ordL x = 0 := by
  have hv : Valued.v x ≠ 0 := by rw [h]; exact one_ne_zero
  unfold ordL
  rw [dite_eq_right hv]
  have e : WithZero.unzero hv = 1 := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, h]
    rfl
  rw [e]
  simp

theorem det_mem {w : Pl E} {n : ℕ} {M : Matrix (Fin n) (Fin n) (w.adicCompletion E)}
    (hM : ∀ i j, M i j ∈ Ov E w) : M.det ∈ Ov E w := by
  rw [Matrix.det_apply']
  exact Subring.sum_mem _ fun σ _ => Subring.mul_mem _ (intCast_mem _ _)
    (Subring.prod_mem _ fun i _ => hM _ _)

theorem v_det {w : Pl E} {n : ℕ} {g : GLw n w} (hg : g ∈ GlobalTheory.LFun.KGL w (n := n)) : Valued.v g.val.det = 1 := by
  obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hg
  have d1 : Valued.v g.val.det ≤ 1 := det_mem h1
  have d2 : Valued.v (g⁻¹).val.det ≤ 1 := det_mem h2
  have e : g.val.det * (g⁻¹).val.det = 1 := by
    rw [← Matrix.det_mul, show g.val * (g⁻¹).val = 1 from g.mul_inv, Matrix.det_one]
  have e' : Valued.v g.val.det * Valued.v (g⁻¹).val.det = 1 := by
    rw [← map_mul, e, map_one]
  refine le_antisymm d1 ?_
  calc (1 : _) = Valued.v g.val.det * Valued.v (g⁻¹).val.det := e'.symm
    _ ≤ Valued.v g.val.det * 1 := mul_le_mul_right d2 _
    _ = _ := mul_one _

def cMu {a b : ℕ} {w : Pl E} (μ : (w.adicCompletion E)ˣ →* ℂˣ) (m : GLw a w × GLw b w) : ℂ :=
  (μ ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂ)

theorem mu_unit {a b : ℕ} {w : Pl E} {μ : (w.adicCompletion E)ˣ →* ℂˣ}
    (hμ : ∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → μ u = 1)
    {κ : GLw a w × GLw b w} (hκ : κ ∈ K2 a b w) :
    μ (GeneralLinearGroup.det κ.1 ^ b * GeneralLinearGroup.det κ.2 ^ a) = 1 := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hκ
  refine hμ _ (ordL_eq_zero ?_)
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, GeneralLinearGroup.val_det_apply, map_mul, map_pow,
    v_det h1, v_det h2, one_pow, one_mul]

theorem cMu_mul_left {a b : ℕ} {w : Pl E} {μ : (w.adicCompletion E)ˣ →* ℂˣ}
    (hμ : ∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → μ u = 1)
    {κ : GLw a w × GLw b w} (hκ : κ ∈ K2 a b w) (m : GLw a w × GLw b w) : cMu μ (κ * m) = cMu μ m := by
  unfold cMu
  have e : ((-1) ^ (a * b) * GeneralLinearGroup.det (κ * m).1 ^ b * GeneralLinearGroup.det (κ * m).2 ^ a :
      (w.adicCompletion E)ˣ) = ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) *
        (GeneralLinearGroup.det κ.1 ^ b * GeneralLinearGroup.det κ.2 ^ a) := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_pow]
    ac_rfl
  rw [e, map_mul, mu_unit hμ hκ, mul_one]

theorem cMu_mul_right {a b : ℕ} {w : Pl E} {μ : (w.adicCompletion E)ˣ →* ℂˣ}
    (hμ : ∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → μ u = 1)
    {κ : GLw a w × GLw b w} (hκ : κ ∈ K2 a b w) (m : GLw a w × GLw b w) : cMu μ (m * κ) = cMu μ m := by
  unfold cMu
  have e : ((-1) ^ (a * b) * GeneralLinearGroup.det (m * κ).1 ^ b * GeneralLinearGroup.det (m * κ).2 ^ a :
      (w.adicCompletion E)ˣ) = ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) *
        (GeneralLinearGroup.det κ.1 ^ b * GeneralLinearGroup.det κ.2 ^ a) := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_pow]
    ac_rfl
  rw [e, map_mul, mu_unit hμ hκ, mul_one]

theorem hasCompactSupport_Tj {w : Pl E} {n : ℕ} {ϖ : w.adicCompletion E} (h0 : ϖ ≠ 0) (k : ℕ) :
    HasCompactSupport (Tj ℂ n (Ov E w) ϖ k : GLw n w → ℂ) := by
  have hdet : (diagJ n ϖ k).det ≠ 0 := by
    rw [diagJ, Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    split_ifs
    · exact h0
    · exact one_ne_zero
  set t : GLw n w := GeneralLinearGroup.mkOfDetNeZero (diagJ n ϖ k) hdet with ht
  have hI := GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w n
  have hS : IsCompact ((fun p : GLw n w × GLw n w => p.1 * t * p.2) ''
      ((GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) ×ˢ (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)))) :=
    (hI.prod hI).image ((continuous_fst.mul continuous_const).mul continuous_snd)
  refine HasCompactSupport.intro' hS hS.isClosed fun g hg => ?_
  unfold Tj
  refine Set.indicator_of_notMem ?_ _
  rintro ⟨x, hx, y, hy, e⟩
  exact hg ⟨(x, y), ⟨hx, hy⟩, Units.ext (by simpa [ht] using e.symm)⟩

theorem blk_zero_mem {a b n : ℕ} (h : a + b = n) (w : Pl E) {κ : GLw a w × GLw b w} (hκ : κ ∈ K2 a b w) :
    blk h w κ 0 ∈ GlobalTheory.LFun.KGL w (n := n) := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hκ
  obtain ⟨l1, l2⟩ := GlobalTheory.BCT.CtLevel.lev_KGL_of_unram E a b n h w 1 (fun _ _ => rfl)
  have d1 : GlobalTheory.BCT.CtLevel.dgM h w (κ.1, 1) ∈ GlobalTheory.LFun.KGL w (n := n) := by
    have : κ.1 ∈ GlobalTheory.BCT.CtLevel.lev₁ h w (GlobalTheory.LFun.KGL w (n := n)) 1 := by rw [l1]; exact h1
    exact this.1.2
  have d2 : GlobalTheory.BCT.CtLevel.dgM h w (1, κ.2) ∈ GlobalTheory.LFun.KGL w (n := n) := by
    have : κ.2 ∈ GlobalTheory.BCT.CtLevel.lev₂ h w (GlobalTheory.LFun.KGL w (n := n)) 1 := by rw [l2]; exact h2
    exact this.1.2
  rw [GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.blk_zero_eq]
  have e : κ = (κ.1, 1) * (1, κ.2) := by simp
  rw [e, map_mul]
  exact mul_mem d1 d2

theorem ctT_eq {n a b : ℕ} (h : a + b = n) {w : Pl E} (hw : IsSplitAt w) (μ : (w.adicCompletion E)ˣ →* ℂˣ)
    {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) (k : ℕ) :
    RS.ctT h w μ ϖ k = fun m => cMu μ m * phi3 h w (Tj ℂ n (Ov E w) ϖ k) 1 1 m := by
  funext m
  rw [GlobalTheory.CompanionTheory.CtS.ctT_split_eq E n a b h w μ ϖ hw hϖ k m]
  simp [phi3, cMu]

theorem isHecke_ctT : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (ϖ : (w.adicCompletion E)ˣ), IsSplitAt w → ordL (ϖ : w.adicCompletion E) = 1 → (∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → μ u = 1) → ∀ k : ℕ, IsHecke (K2 a b w) (RS.ctT h w μ (ϖ : w.adicCompletion E) k) := by
  intro E _ _ _ n a b h w μ ϖ hw hord hμ k
  have h0 : (ϖ : w.adicCompletion E) ≠ 0 := ϖ.ne_zero
  have hϖ : IsUnifV E w (ϖ : w.adicCompletion E) := isUnifV_of_ordL h0 hord
  have hT := Tj_mem_hecke (n := n) hϖ k
  have hf : ∀ k₁ ∈ GlobalTheory.LFun.KGL w (n := n), ∀ k₂ ∈ GlobalTheory.LFun.KGL w (n := n), ∀ g : GLw n w,
      Tj ℂ n (Ov E w) (ϖ : w.adicCompletion E) k (k₁ * g * k₂) = Tj ℂ n (Ov E w) (ϖ : w.adicCompletion E) k g :=
    fun k₁ h₁ k₂ h₂ g => hT.1 ⟨k₁, h₁⟩ ⟨k₂, h₂⟩ g
  have hbi := GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.constant_term_bi_invariant (a := a) (b := b) h w (GlobalTheory.LFun.KGL w (n := n)) le_rfl
    (fun k hk k' hk' => mul_mem (mul_mem hk hk') (inv_mem hk)) _ hf 1 1 (one_mem _) (one_mem _)
  have hone : (1 : GLw a w × GLw b w) ∈ leviOf h w (GlobalTheory.LFun.KGL w (n := n)) := blk_zero_mem h w (one_mem _)
  rw [ctT_eq h hw μ hϖ k]
  refine ⟨?_, fun κ hκ x => ⟨?_, ?_⟩⟩
  · exact (GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.constant_term_compact_support h w _ (hasCompactSupport_Tj h0 k) 1 1).mul_left
  · have := hbi κ 1 (blk_zero_mem h w hκ) hone x
    rw [mul_one] at this
    simp only [cMu_mul_left hμ hκ, this]
  · have := hbi 1 κ hone (blk_zero_mem h w hκ) x
    rw [one_mul] at this
    simp only [cMu_mul_right hμ hκ, this]

end GlobalTheory.CompanionTheory.CtHecke
end
end

section

noncomputable section

open scoped Topology
open Filter Set Metric GlobalTheory.Cont

namespace GlobalTheory.CompanionTheory.DivMult

theorem exists_factor {A : ℂ → ℂ} (hA : Differentiable ℂ A) (hne : ∃ z, A z ≠ 0) (s₀ : ℂ) :
    ∃ (k : ℕ) (u : ℂ → ℂ) (r M : ℝ), 0 < r ∧ DifferentiableOn ℂ u (ball s₀ r) ∧ (∀ s ∈ ball s₀ r, u s ≠ 0) ∧
      (∀ s ∈ ball s₀ r, A s = (s - s₀) ^ k * u s) ∧ ∀ s ∈ ball s₀ r, ‖(u s)⁻¹‖ ≤ M := by
  have hAn : AnalyticOnNhd ℂ A univ := fun z _ => hA.analyticAt z
  have hnz : ¬∀ᶠ z in 𝓝 s₀, A z = 0 := by
    intro hev
    obtain ⟨w, hw⟩ := hne
    have := hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ s₀)
      (hev.mono fun z hz => by simp [hz])
    exact hw (by simpa using this (mem_univ w))
  obtain ⟨k, g, hg, hg0, hev⟩ := (hA.analyticAt s₀).exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnz
  have hpos : 0 < ‖g s₀‖ := norm_pos_iff.mpr hg0
  have hcont : ∀ᶠ z in 𝓝 s₀, ‖g z - g s₀‖ < ‖g s₀‖ / 2 := by
    have h2 : ball (g s₀) (‖g s₀‖ / 2) ∈ 𝓝 (g s₀) := ball_mem_nhds _ (by positivity)
    filter_upwards [hg.continuousAt h2] with z hz
    simpa [dist_eq_norm] using hz
  obtain ⟨r, hr, hball⟩ :=
    Metric.eventually_nhds_iff_ball.mp (hev.and (hcont.and hg.eventually_analyticAt))
  refine ⟨k, g, r, 2 / ‖g s₀‖, hr, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (hball z hz).2.2.differentiableAt.differentiableWithinAt
  · intro z hz h0
    have h1 := (hball z hz).2.1
    rw [h0, zero_sub, norm_neg] at h1
    linarith
  · intro z hz
    simpa [smul_eq_mul] using (hball z hz).1
  · intro z hz
    have h1 := (hball z hz).2.1
    have hlow : ‖g s₀‖ / 2 ≤ ‖g z‖ := by
      have h3 := norm_sub_norm_le (g s₀) (g z)
      rw [norm_sub_rev] at h3
      linarith
    calc ‖(g z)⁻¹‖ = ‖g z‖⁻¹ := norm_inv _
      _ ≤ (‖g s₀‖ / 2)⁻¹ := inv_anti₀ (by positivity) hlow
      _ = 2 / ‖g s₀‖ := inv_div _ _

def glue (h F A : ℂ → ℂ) (R : ℝ) (z : ℂ) : ℂ := if R < z.re then h z else F z / A z

variable {h F A : ℂ → ℂ} {R : ℝ}

theorem glue_eq (he : ∀ z : ℂ, R < z.re → F z = A z * h z) {z : ℂ} (hz : A z ≠ 0) : glue h F A R z = F z / A z := by
  unfold glue
  split_ifs with c
  · rw [he z c, mul_div_cancel_left₀ _ hz]
  · rfl

theorem glue_eventuallyEq (hA : Differentiable ℂ A) (hne : ∃ z, A z ≠ 0) (he : ∀ z : ℂ, R < z.re → F z = A z * h z) (s : ℂ) :
    glue h F A R =ᶠ[𝓝[≠] s] fun z => F z / A z := by
  have hAn : AnalyticOnNhd ℂ A univ := fun z _ => hA.analyticAt z
  rcases (hA.analyticAt s).eventually_eq_zero_or_eventually_ne_zero with hev | hev
  · exfalso
    obtain ⟨w, hw⟩ := hne
    have := hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ s)
      (hev.mono fun z hz => by simp [hz])
    exact hw (by simpa using this (mem_univ w))
  · filter_upwards [hev] with z hz using glue_eq he hz

theorem isMerExt_glue (hA : Differentiable ℂ A) (hne : ∃ z, A z ≠ 0) (hF : Differentiable ℂ F)
    (he : ∀ z : ℂ, R < z.re → F z = A z * h z) : IsMerExt h univ (glue h F A R) := by
  refine ⟨isRightDomain_univ, fun s _ => ?_, ⟨R, fun z hz => ?_⟩⟩
  · have hm : MeromorphicAt (fun z => F z / A z) s :=
      (hF.analyticAt s).meromorphicAt.div (hA.analyticAt s).meromorphicAt
    exact hm.congr (glue_eventuallyEq hA hne he s).symm
  · have hz' : R < z.re := hz
    simp [glue, hz']

theorem cont_eq_div (hA : Differentiable ℂ A) (hne : ∃ z, A z ≠ 0) (hF : Differentiable ℂ F)
    (he : ∀ z : ℂ, R < z.re → F z = A z * h z) {s : ℂ} (hs : A s ≠ 0) : cont h s = F s / A s := by
  have hM := isMerExt_glue hA hne hF he
  have hE : IsExtAt h s (glue h F A R) := hM.isExtAt (mem_univ s)
  have hcont : ContinuousAt (fun z => F z / A z) s :=
    hF.continuous.continuousAt.div hA.continuous.continuousAt hs
  have ht : Tendsto (glue h F A R) (𝓝[≠] s) (𝓝 (F s / A s)) :=
    Tendsto.congr' (glue_eventuallyEq hA hne he s).symm (hcont.tendsto.mono_left nhdsWithin_le_nhds)
  exact (hE.holValueAt_iff.mpr ht).valueAt.cont_eq

theorem div_multiplier : ResidueKilled.Tr.Div := by
  unfold ResidueKilled.Tr.Div
  intro D T e H A R hA hne hH hHc hmul hbd
  unfold GlobalTheory.EisCont.ContMod GlobalTheory.Cont.Continues
  refine ⟨fun g => ⟨_, isMerExt_glue hA hne (hH g) (fun z hz => hmul z hz g)⟩, fun s₀ => ?_⟩
  obtain ⟨k, u, r, M, hr, hu, hu0, hfac, hM⟩ := exists_factor hA hne s₀
  obtain ⟨C, N, hCN⟩ := hbd (‖s₀‖ + r)
  have hu1 : ContinuousOn (fun x : ℂ × _ => u x.1) (ball s₀ r ×ˢ (univ : Set (Formalism.L2.Theta.GA D T))) :=
    hu.continuousOn.comp continuous_fst.continuousOn (fun x hx => hx.1)
  unfold GlobalTheory.EisCont.RegAt
  refine ⟨k, r, fun s g => H s g * (u s)⁻¹, hr, ?_, ?_, ?_, C * M, N, ?_⟩
  · intro s hs hss g
    have hAs : A s = (s - s₀) ^ k * u s := hfac s hs
    have hus : u s ≠ 0 := hu0 s hs
    have hpow : (s - s₀) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hss)
    have hA0 : A s ≠ 0 := by rw [hAs]; exact mul_ne_zero hpow hus
    show H s g * (u s)⁻¹ = (s - s₀) ^ k * cont (fun z => e z g) s
    rw [cont_eq_div hA hne (hH g) (fun z hz => hmul z hz g) hA0, hAs]
    field_simp
    try ring
  · intro g
    exact (hH g).differentiableOn.mul (hu.inv hu0)
  · exact hHc.continuousOn.mul (hu1.inv₀ (fun x hx => hu0 x.1 hx.1))
  · intro s hs g
    have hs1 : ‖s - s₀‖ < r := by simpa [dist_eq_norm] using hs
    have hs2 := norm_sub_norm_le s s₀
    have hsr : ‖s‖ ≤ ‖s₀‖ + r := by linarith
    have hH1 := hCN s hsr g
    have hM1 := hM s hs
    show ‖H s g * (u s)⁻¹‖ ≤ C * M * GlobalTheory.Grow.height T g ^ N
    calc ‖H s g * (u s)⁻¹‖ = ‖H s g‖ * ‖(u s)⁻¹‖ := norm_mul _ _
      _ ≤ (C * GlobalTheory.Grow.height T g ^ N) * M := mul_le_mul hH1 hM1 (norm_nonneg _) (le_trans (norm_nonneg _) hH1)
      _ = C * M * GlobalTheory.Grow.height T g ^ N := by ring

end GlobalTheory.CompanionTheory.DivMult

end
end
