module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle010
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle199
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle198
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle108
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaOfLinearReductive
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle286
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle398
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ConstantTermSteps.UnipGLMemAdelicBorel
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle392
public import Development.WeilBound.CoreStatements.BranchingTraces.HilbertSchmidtTraces.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeAntidiagFixed
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle394
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.IsStrictDom

@[expose] public section

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.AdmGL

variable {ι : Type} [Fintype ι] [DecidableEq ι] {a n : ℕ}


open scoped Classical in
def toGL (M : Matrix (Fin a) (Fin a) (ι → ℂ)) : GL (Fin a) (ι → ℂ) :=
  if h : IsUnit M then h.unit else 1

theorem coe_toGL {M : Matrix (Fin a) (Fin a) (ι → ℂ)} (h : IsUnit M) : (toGL M : Matrix (Fin a) (Fin a) (ι → ℂ)) = M := by
  simp [toGL, h]

theorem toGL_coe (u : GL (Fin a) (ι → ℂ)) : toGL (u : Matrix (Fin a) (Fin a) (ι → ℂ)) = u :=
  Units.ext (coe_toGL u.isUnit)

def blkRep {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e : Fin a × ι ≃ Fin n)
    (σ : GL (Fin a) (ι → ℂ) →* (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ) : H →L[ℂ] H :=
  σ (toGL (unblk e g))

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem blkRep_blk (e : Fin a × ι ≃ Fin n) (σ : GL (Fin a) (ι → ℂ) →* (H →L[ℂ] H)) (u : GL (Fin a) (ι → ℂ)) :
    blkRep e σ (blk e (u : Matrix (Fin a) (Fin a) (ι → ℂ))) = σ u := by
  rw [blkRep, unblk_blk, toGL_coe]

theorem blk_coe_mem (e : Fin a × ι ≃ Fin n) (u : GL (Fin a) (ι → ℂ)) :
    blk e (u : Matrix (Fin a) (Fin a) (ι → ℂ)) ∈ blkG e := ⟨_, u.isUnit, rfl⟩

theorem exists_gl_of_mem (e : Fin a × ι ≃ Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ blkG e) :
    ∃ u : GL (Fin a) (ι → ℂ), g = blk e (u : Matrix (Fin a) (Fin a) (ι → ℂ)) := by
  obtain ⟨M, hM, rfl⟩ := hg
  exact ⟨hM.unit, rfl⟩

theorem continuousOn_toGL_unblk (e : Fin a × ι ≃ Fin n) :
    ContinuousOn (fun g => toGL (unblk e g) : Matrix (Fin n) (Fin n) ℂ → GL (Fin a) (ι → ℂ)) (blkG e) := by
  rw [continuousOn_iff_continuous_restrict]
  have hval : ∀ g : blkG e, ((toGL (unblk e g.1) : GL (Fin a) (ι → ℂ)) : Matrix (Fin a) (Fin a) (ι → ℂ)) = unblk e g.1 := by
    rintro ⟨_, M, hM, rfl⟩
    rw [unblk_blk]
    exact coe_toGL hM
  have hinv : ∀ g : blkG e, (((toGL (unblk e g.1))⁻¹ : GL (Fin a) (ι → ℂ)) : Matrix (Fin a) (Fin a) (ι → ℂ)) =
      unblk e (g.1.det⁻¹ • g.1.adjugate) := by
    rintro ⟨_, M, hM, rfl⟩
    have h := blk_inv e hM
    rw [Matrix.inv_def, Ring.inverse_eq_inv'] at h
    simp only [h, unblk_blk]
    rw [Matrix.coe_units_inv, coe_toGL hM]
  have hdet : ∀ g : blkG e, g.1.det ≠ 0 := fun g =>
    ((Matrix.isUnit_iff_isUnit_det _).1 ((mem_blkG_iff e).1 g.2).1).ne_zero
  have hc : Continuous fun g : blkG e => g.1.det⁻¹ • g.1.adjugate :=
    (Continuous.inv₀ continuous_subtype_val.matrix_det hdet).smul continuous_subtype_val.matrix_adjugate
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact ((continuous_unblk e).comp continuous_subtype_val).congr fun g => (hval g).symm
  · exact ((continuous_unblk e).comp hc).congr fun g => (hinv g).symm

theorem isURepOn_blkRep (e : Fin a × ι ≃ Fin n) {σ : GL (Fin a) (ι → ℂ) →* (H →L[ℂ] H)} (hσ : IsUnitaryRep σ) :
    Formalism.MainNotions.S.IsURepOn (blkG e) (blkRep e σ) := by
  refine ⟨⟨?_, ?_⟩, fun g _ v => hσ.norm_apply _ v, fun v =>
    (hσ.continuous_apply v).comp_continuousOn (continuousOn_toGL_unblk e)⟩
  · have h := blkRep_blk e σ 1
    simpa using h
  · intro g hg h hh
    obtain ⟨u, rfl⟩ := exists_gl_of_mem e hg
    obtain ⟨v, rfl⟩ := exists_gl_of_mem e hh
    rw [← blk_mul, ← Units.val_mul, blkRep_blk, blkRep_blk, blkRep_blk, map_mul]
    rfl

theorem isIrredOn_blkRep (e : Fin a × ι ≃ Fin n) {σ : GL (Fin a) (ι → ℂ) →* (H →L[ℂ] H)}
    (hi : IsTopIrreducible σ) : Formalism.MainNotions.S.IsIrredOn (blkG e) (blkRep e σ) := fun S hS hinv =>
  hi.2 S ⟨hS, fun u v hv => by
    have h := hinv _ (blk_coe_mem e u) v hv
    rwa [blkRep_blk] at h⟩

theorem blk_mem_maxCpt (e : Fin a × ι ≃ Fin n) (k : Matrix.unitaryGroup (Fin a) (ι → ℂ)) :
    blk e k.1 ∈ GlobalTheory.LinRed.maxCpt (blkG e) := by
  refine ⟨blk_coe_mem e (Unitary.toUnits k), ?_⟩
  rw [SetLike.mem_coe, Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← blk_conjTranspose, ← blk_mul,
    ← Matrix.star_eq_conjTranspose, (Matrix.mem_unitaryGroup_iff).1 k.2, blk_one]

theorem exists_unitary_of_mem_maxCpt (e : Fin a × ι ≃ Fin n) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ GlobalTheory.LinRed.maxCpt (blkG e)) :
    ∃ k : Matrix.unitaryGroup (Fin a) (ι → ℂ), g = blk e k.1 := by
  obtain ⟨⟨M, -, rfl⟩, hu⟩ := hg
  refine ⟨⟨M, ?_⟩, rfl⟩
  rw [SetLike.mem_coe, Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← blk_conjTranspose, ← blk_mul,
    ← blk_one e, ← Matrix.star_eq_conjTranspose] at hu
  rw [Matrix.mem_unitaryGroup_iff]
  exact blk_injective e hu

theorem finiteDimensional_isoPart_gl [CompleteSpace H] {σ : GL (Fin a) (ι → ℂ) →* (H →L[ℂ] H)}
    (hσ : IsUnitaryRep σ) (hi : IsTopIrreducible σ) {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin a) (ι → ℂ)) W) :
    FiniteDimensional ℂ (isoPart (σ.comp Unitary.toUnits) ρ) := by
  let e := Fintype.equivFin (Fin a × ι)
  have hLR : GlobalTheory.LinRed.IsLinRed (blkG e) := by
    refine
      { one_mem := ⟨1, isUnit_one, blk_one e⟩
        mul_mem := ?_
        isUnit := fun g hg => ((mem_blkG_iff e).1 hg).1
        inv_mem := ?_
        closed := fun g hg hcl => (mem_blkG_iff e).2 ⟨hg, blk_unblk_of_mem_closure e hcl⟩
        connected := isPreconnected_blkG e
        star_mem := ?_ }
    · rintro _ ⟨M, hM, rfl⟩ _ ⟨N, hN, rfl⟩
      exact ⟨M * N, IsUnit.mul hM hN, blk_mul e M N⟩
    · rintro _ ⟨M, hM, rfl⟩
      exact ⟨M⁻¹, (Matrix.isUnit_nonsing_inv_iff).2 hM, (blk_inv e hM).symm⟩
    · rintro _ ⟨M, hM, rfl⟩
      exact ⟨Mᴴ, IsUnit.star hM, blk_conjTranspose e M⟩
  have hA := GlobalTheory.CompanionTheory.admitted.isAdmissible_of_unitary_irreducible hLR
    (GlobalTheory.CompanionTheory.AdmIwa.RamifiedPrimeLengthBound hLR (GlobalTheory.CompanionTheory.IwaGen.iwaOn_of_isLinRed hLR)) H (blkRep e σ)
    (isURepOn_blkRep e hσ) (isIrredOn_blkRep e hi)
  have hrep : ∀ k : Matrix.unitaryGroup (Fin a) (ι → ℂ),
      blkRep e σ (blk e k.1) = (σ.comp Unitary.toUnits) k := fun k => blkRep_blk e σ (Unitary.toUnits k)
  refine finiteDimensional_isoPart (π := σ.comp Unitary.toUnits) (fun k v => hσ.norm_apply _ v) ?_ _ W ρ rfl
  intro S hfd hS hirr
  have hKS : GlobalTheory.LinRed.IsKStable (blkG e) (blkRep e σ) S := by
    intro g hg w hw
    obtain ⟨k, rfl⟩ := exists_unitary_of_mem_maxCpt e hg
    rw [hrep]
    exact hS k w hw
  have hirr' : ∀ S' : Submodule ℂ H, S' ≤ S → GlobalTheory.LinRed.IsKStable (blkG e) (blkRep e σ) S' → S' = ⊥ ∨ S' = S :=
    fun S' hle hst => hirr S' hle fun k w hw => by
      have h := hst _ (blk_mem_maxCpt e k) w hw
      rwa [hrep] at h
  have hfin := hA.2.2.2 S hfd hKS hirr'
  have heq : {S' : Submodule ℂ H | ∃ T : H →ₗ[ℂ] H, S' = S.map T ∧
      ∀ k, ∀ w ∈ S, T ((σ.comp Unitary.toUnits) k w) = (σ.comp Unitary.toUnits) k (T w)} =
      {S' | ∃ T : H →ₗ[ℂ] H, S' = S.map T ∧ ∀ k ∈ GlobalTheory.LinRed.maxCpt (blkG e), ∀ w ∈ S,
        T (blkRep e σ k w) = blkRep e σ k (T w)} := by
    ext S'
    constructor
    · rintro ⟨T, rfl, hT⟩
      refine ⟨T, rfl, fun g hg w hw => ?_⟩
      obtain ⟨k, rfl⟩ := exists_unitary_of_mem_maxCpt e hg
      rw [hrep]
      exact hT k w hw
    · rintro ⟨T, rfl, hT⟩
      refine ⟨T, rfl, fun k w hw => ?_⟩
      rw [← hrep]
      exact hT _ (blk_mem_maxCpt e k) w hw
  rw [heq]
  exact hfin

theorem admissible_GL_Cinf : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : GL (Fin a) (Cinf E) →* (H →L[ℂ] H)), IsUnitaryRep σ → IsTopIrreducible σ → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W), FiniteDimensional ℂ ↥(⨆ (T : W →ₗ[ℂ] H) (_ : ∀ k w, T (ρ k w) = σ (Unitary.toUnits k) (T w)), LinearMap.range T : Submodule ℂ H) := by
  intro E _ _ _ a H _ _ _ σ hσ hi W _ _ _ ρ
  classical
  exact finiteDimensional_isoPart_gl hσ hi ρ

end GlobalTheory.CompanionTheory.AdmGL

end
end

section

noncomputable section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
open PositivityTheory.Rg.Rs.An PositivityTheory.Rg.Rs.ctstepglue

namespace GlobalTheory.CompanionTheory.Conc

theorem ubnd_ctn {K : Type} [Field K] [NumberField K] {n : ℕ} {ι : Type}
    {r : ℕ} {f : ι → AdelicGLn.AdelicGL K n → ℂ} {m : ℕ → ℝ} (h : UBnd f m) :
    UBnd (fun i => An.ctn r (f i)) m := by
  intro ω hω hωB t₀ Q hQ
  obtain ⟨D, hD, hFD⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := n) (r := r)
  set ω' := (fun p : (UPos n r → NumberField.AdeleRing (𝓞 K) K) × AdelicGLn.AdelicGL K n => unipGL p.1 * p.2) '' (D ×ˢ ω)
  have hω' : IsCompact ω' :=
    (hD.prod hω).image ((continuous_unipGL.comp continuous_fst).mul continuous_snd)
  have hω'B : ω' ⊆ (adelicBorel (K := K) (n := n) : Set _) := by
    rintro _ ⟨⟨X, b⟩, ⟨hX, hb⟩, rfl⟩
    exact mul_mem (unipGL_mem_adelicBorel r X) (hωB hb)
  obtain ⟨C, hC⟩ := h ω' hω' hω'B t₀ Q hQ
  refine ⟨max C 0, fun i b hb x hx q hq => ?_⟩
  refine norm_ctn_le (f i) hD hFD _ (by positivity) fun X hX => ?_
  have := hC i (unipGL X * b) ⟨(X, b), ⟨hX, hb⟩, rfl⟩ x hx q hq
  rw [← mul_assoc, ← mul_assoc]
  exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)

theorem ubnd_ctn_step : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ι : Type) (f : ι → AdelicGLn.AdelicGL K n → ℂ) (m : ℕ → ℝ) (r D : ℕ) (κ' κ : ℝ) (p : ι → ℂ[X]),
  0 < r → r < n → UFam f → UBnd f m → κ' < κ →
  (∀ i, (p i).Monic ∧ (p i).natDegree ≤ D ∧ An.Kill r (f i) (p i) ∧ ∀ z, (p i).IsRoot z → ‖z‖ ≤ Real.exp κ') →
  UBnd (fun i => An.ctn r (f i)) (Function.update m r κ) := by
  intro K _ _ n ι f m r D κ' κ pf hr hrn hf hB hκ hpf ω hω hωB t₀ Q hQ
  obtain ⟨C₁, hC₁⟩ := ubnd_ctn (r := r) hB ω hω hωB t₀ Q hQ
  obtain ⟨C₂, hC₂0, hC₂⟩ := GlobalTheory.T.linear_recurrence_growth_bound D κ' κ hκ
  set E : ℝ := Real.exp (|m r| * (|t₀| + 1 + D)) with hE
  refine ⟨C₂ * (max C₁ 0 * E) * Real.exp (|κ| * (|t₀| + 1)), ?_⟩
  intro a b hb x hx q hq
  obtain ⟨hp, hdD, hK, hroot⟩ := hpf a
  set p := pf a with hpdef
  set φ := f a with hφdef
  set d := p.natDegree with hd
  set S : ℝ := ∑ r' ∈ (Finset.range n).erase r, m r' * sr x r' with hS
  have hrmem : r ∈ Finset.range n := Finset.mem_range.2 hrn
  have hsum : ∀ (f : ℕ → ℝ) (y : Fin n → ℝ), (∀ r' ≠ r, f r' = m r') → (∀ r' ≠ r, sr y r' = sr x r') →
      ∑ r' ∈ Finset.range n, f r' * sr y r' = f r * sr y r + S := by
    intro f y hf hy
    rw [← Finset.add_sum_erase _ _ hrmem, hS]
    congr 1
    refine Finset.sum_congr rfl fun r' h' => ?_
    rw [hf r' (Finset.ne_of_mem_erase h'), hy r' (Finset.ne_of_mem_erase h')]
  have h0 : 0 ≤ sr x r + t₀ := by linarith [hx r]
  set i : ℕ := ⌊sr x r + t₀⌋₊ with hi
  have hi1 : (i : ℝ) ≤ sr x r + t₀ := Nat.floor_le h0
  have hi2 : sr x r + t₀ < i + 1 := Nat.lt_floor_add_one _
  set x' : Fin n → ℝ := shift r x (-(i : ℝ)) with hx'
  set g₀ : AdelicGLn.AdelicGL K n := b * tor K x' * q with hg₀
  set u : ℕ → ℂ := fun k => ctn r φ (aR K n r k * g₀) with hu
  have hrecu : ∀ k, ∑ j ∈ Finset.range (d + 1), p.coeff j * u (k + j) = 0 := by
    intro k
    have := hK (aR K n r k * g₀)
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hu, ← mul_assoc, aR_mul]
    congr 4
    push_cast; ring

  have hmove : ∀ (t : ℝ) (h : AdelicGLn.AdelicGL K n), ctn r φ (aR K n r t * (b * h)) = ctn r φ (b * (aR K n r t * h)) := by
    intro t h
    obtain ⟨X, hX⟩ := borel_aR (r := r) (hωB hb) t
    have : aR K n r t * b = unipGL (-X) * (b * aR K n r t) := by
      rw [hX, ← mul_assoc, ← unipGL_add, neg_add_cancel, unipGL_zero, one_mul]
    rw [← mul_assoc, this, mul_assoc, ctn_unipGL_mul (hf.left a), ← mul_assoc]
  set M : ℝ := max C₁ 0 * E * Real.exp S with hM
  have hM0 : 0 ≤ M := by positivity
  have hinit : ∀ j < d, ‖u j‖ ≤ M := by
    intro j hj
    have e1 : u j = ctn r φ (b * tor K (shift r x ((j : ℝ) - i)) * q) := by
      simp only [hu, hg₀, mul_assoc]
      rw [hmove, ← mul_assoc (aR K n r j), ← tor_shift, hx',
        show shift r (shift r x (-(i : ℝ))) (j : ℝ) = shift r x ((j : ℝ) - i) from by
          funext l; simp only [shift]; split_ifs <;> ring]
    have hsr : ∀ r', sr (shift r x ((j : ℝ) - i)) r' = sr x r' + if r' = r then (j : ℝ) - i else 0 :=
      sr_shift hr hrn x _
    have hx2 : ∀ r', -t₀ ≤ sr (shift r x ((j : ℝ) - i)) r' := by
      intro r'
      rw [hsr]
      split_ifs with h
      · subst h; have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith
      · simpa using hx r'
    have hb1 := hC₁ a b hb _ hx2 q hq
    rw [e1]
    refine hb1.trans ?_
    rw [hsum m _ (fun _ _ => rfl) (fun r' h => by rw [hsr, if_neg h, add_zero]), hsr, if_pos rfl,
      Real.exp_add, hM, ← mul_assoc]
    have hjd : (j : ℝ) ≤ D := by exact_mod_cast (hj.le.trans hdD)
    have hv : |sr x r + ((j : ℝ) - i)| ≤ |t₀| + 1 + D := by
      rw [abs_le]; constructor <;> cases abs_cases t₀ <;> linarith
    have hexp : Real.exp (m r * (sr x r + ((j : ℝ) - i))) ≤ E := by
      rw [hE]; apply Real.exp_le_exp.2
      calc m r * (sr x r + ((j : ℝ) - i)) ≤ |m r * (sr x r + ((j : ℝ) - i))| := le_abs_self _
        _ = |m r| * |sr x r + ((j : ℝ) - i)| := abs_mul _ _
        _ ≤ |m r| * (|t₀| + 1 + D) := mul_le_mul_of_nonneg_left hv (abs_nonneg _)
    have hC : C₁ ≤ max C₁ 0 := le_max_left _ _
    gcongr
  have hmain := hC₂ p hp hdD hroot u M hrecu hinit hM0 i
  have heq : ctn r φ (b * tor K x * q) = u i := by
    have : x = shift r x' (i : ℝ) := by
      funext l; simp only [hx', shift]; split_ifs <;> ring
    simp only [hu, hg₀]
    conv_lhs => rw [this, tor_shift]
    rw [mul_assoc b (tor K x') q, hmove]
    simp only [mul_assoc]
  show ‖ctn r φ (b * tor K x * q)‖ ≤ _
  rw [heq]
  refine hmain.trans ?_
  rw [hsum (Function.update m r κ) x (fun r' h => Function.update_of_ne h _ _) (fun _ _ => rfl),
    Function.update_self, Real.exp_add, hM]
  have hk : Real.exp (κ * i) ≤ Real.exp (κ * sr x r) * Real.exp (|κ| * (|t₀| + 1)) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2
    have : |(i : ℝ) - sr x r| ≤ |t₀| + 1 := by
      rw [abs_le]; constructor <;> cases abs_cases t₀ <;> linarith
    have := mul_le_mul_of_nonneg_left this (abs_nonneg κ)
    have h2 : κ * ((i : ℝ) - sr x r) ≤ |κ| * |(i : ℝ) - sr x r| := by
      rw [← abs_mul]; exact le_abs_self _
    nlinarith
  have hE0 : 0 ≤ max C₁ 0 * E := by positivity
  calc C₂ * Real.exp (κ * i) * (max C₁ 0 * E * Real.exp S)
      ≤ C₂ * (Real.exp (κ * sr x r) * Real.exp (|κ| * (|t₀| + 1))) * (max C₁ 0 * E * Real.exp S) := by
        gcongr
    _ = C₂ * (max C₁ 0 * E) * Real.exp (|κ| * (|t₀| + 1)) * (Real.exp (κ * sr x r) * Real.exp S) := by ring

end GlobalTheory.CompanionTheory.Conc

end
end

section

noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.RgHeA
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.RgHeA.TwPf

section Unitary

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
  {ρ : Γ → (A →L[ℂ] A)}

theorem inner_map_map (hU : IsU ρ) (g : Γ) (x y : A) : ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ := by
  obtain ⟨_, _, hnorm, _⟩ := hU
  let L : A →ₗᵢ[ℂ] A := ⟨(ρ g : A →ₗ[ℂ] A), hnorm g⟩
  exact L.inner_map_map x y

theorem map_mul_apply (hU : IsU ρ) (g h : Γ) (x : A) : ρ (g * h) x = ρ g (ρ h x) := by
  obtain ⟨_, hmul, _, _⟩ := hU
  rw [hmul, ContinuousLinearMap.mul_apply]

theorem inner_translate (hU : IsU ρ) (a g b : Γ) (u : A) :
    ⟪ρ a u, ρ g (ρ b u)⟫_ℂ = ⟪u, ρ (a⁻¹ * g * b) u⟫_ℂ := by
  have h : ρ g (ρ b u) = ρ a (ρ (a⁻¹ * g * b) u) := by
    rw [← GlobalTheory.CompanionTheory.RgHeA.TwPf.map_mul_apply hU, ← GlobalTheory.CompanionTheory.RgHeA.TwPf.map_mul_apply hU, show a * (a⁻¹ * g * b) = g * b by group]
  rw [h, GlobalTheory.CompanionTheory.RgHeA.TwPf.inner_map_map hU]

end Unitary

theorem coefOp_translate {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (hσ : IsU σ) (hρ : IsU ρ) (w₀ : A) (v : B)
    (hc : Integrable (fun g => star ⟪w₀, σ g w₀⟫_ℂ) ν) (hm : Integrable (fun g => star ⟪v, ρ g v⟫_ℂ) ν) (x y : Γ) :
    ⟪σ x w₀, coefOp ν σ hσ (fun g => star ⟪v, ρ g v⟫_ℂ) hm (σ y w₀)⟫_ℂ =
      star ⟪ρ x⁻¹ v, coefOp ν ρ hρ (fun g => star ⟪w₀, σ g w₀⟫_ℂ) hc (ρ y⁻¹ v)⟫_ℂ := by
  rw [GlobalTheory.CompanionTheory.RgHeA.inner_coefOp, GlobalTheory.CompanionTheory.RgHeA.inner_coefOp]
  simp_rw [GlobalTheory.CompanionTheory.RgHeA.TwPf.inner_translate hσ, GlobalTheory.CompanionTheory.RgHeA.TwPf.inner_translate hρ, inv_inv]
  have key : ∀ F : Γ → ℂ, ∫ g, F (x⁻¹ * g * y) ∂ν = ∫ g, F g ∂ν := fun F =>
    (integral_mul_left_eq_self (fun h => F (h * y)) x⁻¹).trans (integral_mul_right_eq_self F y)
  have hstar : star (∫ g, star ⟪w₀, σ g w₀⟫_ℂ * ⟪v, ρ (x * g * y⁻¹) v⟫_ℂ ∂ν) =
      ∫ g, ⟪w₀, σ g w₀⟫_ℂ * star ⟪v, ρ (x * g * y⁻¹) v⟫_ℂ ∂ν := by
    have h := (integral_conj (μ := ν)
      (f := fun g => star ⟪w₀, σ g w₀⟫_ℂ * ⟪v, ρ (x * g * y⁻¹) v⟫_ℂ)).symm
    simpa [map_mul] using h
  rw [hstar, ← key (fun g => ⟪w₀, σ g w₀⟫_ℂ * star ⟪v, ρ (x * g * y⁻¹) v⟫_ℂ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [show x * (x⁻¹ * g * y) * y⁻¹ = g by group]
  exact mul_comm _ _

end GlobalTheory.CompanionTheory.RgHeA.TwPf
end
end

section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.RgHeA
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.RgHeA

theorem isInvInvariant_of_right_haar {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.IsInvInvariant := by
  haveI : IsFiniteMeasureOnCompacts μ.inv :=
    ⟨fun K hK => by rw [Measure.inv_apply]; exact hK.inv.measure_lt_top⟩
  obtain ⟨c, hc⟩ : ∃ c : NNReal, μ.inv = c • μ := ⟨_, Measure.isMulLeftInvariant_eq_smul μ.inv μ⟩
  have hsq : μ = (c * c) • μ := by
    calc μ = μ.inv.inv := (Measure.inv_inv μ).symm
      _ = (c • μ).inv := by rw [hc]
      _ = c • μ.inv := by rw [Measure.inv_def, Measure.inv_def, Measure.map_smul c measurable_inv.aemeasurable]
      _ = (c * c) • μ := by rw [hc, smul_smul]
  let K := Classical.arbitrary (TopologicalSpace.PositiveCompacts G)
  have hpos : μ K ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'
  have hfin : μ K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have hK : μ K = ((c * c) • μ) K := by rw [← hsq]
  rw [Measure.smul_apply, Measure.nnreal_smul_coe_apply] at hK
  have h1 : ((c * c : NNReal) : ENNReal) = 1 :=
    ((ENNReal.mul_left_inj hpos hfin).1 (by rw [one_mul]; exact hK.symm))
  have hcc : (c : ℝ) * c = 1 := by exact_mod_cast ENNReal.coe_eq_one.1 h1
  have hc1 : c = 1 := by
    have : (c : ℝ) = 1 := by nlinarith [c.coe_nonneg]
    exact_mod_cast this
  exact ⟨by rw [hc, hc1, one_smul]⟩

theorem isSelfAdjoint_coefOp : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (hσ : IsU σ), IsU ρ → ∀ (v : B) (hm : Integrable (fun g => star ⟪v, ρ g v⟫_ℂ) ν),
    IsSelfAdjoint (coefOp ν σ hσ (fun g => star ⟪v, ρ g v⟫_ℂ) hm) := by
  intro Γ _ _ _ _ _ _ _ ν _ _ A B _ _ _ _ _ _ σ ρ hσ hρ v hm
  haveI := GlobalTheory.CompanionTheory.RgHeA.isInvInvariant_of_right_haar ν
  obtain ⟨_, hadj, _, _⟩ := PositivityTheory.UnitaryDecomposition.X4.uRep_of hσ
  obtain ⟨_, hρadj, _, _⟩ := PositivityTheory.UnitaryDecomposition.X4.uRep_of hρ
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro a b
  try simp only [ContinuousLinearMap.coe_coe]
  rw [← inner_conj_symm, GlobalTheory.CompanionTheory.RgHeA.inner_coefOp, GlobalTheory.CompanionTheory.RgHeA.inner_coefOp, ← integral_conj]
  calc ∫ g, (starRingEnd ℂ) (star ⟪v, ρ g v⟫_ℂ * ⟪b, σ g a⟫_ℂ) ∂ν
      = ∫ g, star ⟪v, ρ g⁻¹ v⟫_ℂ * ⟪a, σ g⁻¹ b⟫_ℂ ∂ν := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        have e1 : star ⟪v, ρ g⁻¹ v⟫_ℂ = ⟪v, ρ g v⟫_ℂ := by
          rw [← hρadj]
          exact inner_conj_symm _ _
        have e2 : (starRingEnd ℂ) ⟪b, σ g a⟫_ℂ = ⟪a, σ g⁻¹ b⟫_ℂ := by
          rw [inner_conj_symm, hadj]
        show (starRingEnd ℂ) (star ⟪v, ρ g v⟫_ℂ * ⟪b, σ g a⟫_ℂ) = star ⟪v, ρ g⁻¹ v⟫_ℂ * ⟪a, σ g⁻¹ b⟫_ℂ
        rw [map_mul, e1, e2, starRingEnd_apply, star_star]
    _ = ∫ g, star ⟪v, ρ g v⟫_ℂ * ⟪a, σ g b⟫_ℂ ∂ν :=
        integral_inv_eq_self (fun g => star ⟪v, ρ g v⟫_ℂ * ⟪a, σ g b⟫_ℂ) ν

end GlobalTheory.CompanionTheory.RgHeA
end
end

section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot

theorem _root_.GlobalTheory.T.reflection_root_unipotent_shift : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ) (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (v : GU σ n), IsUnipU v →
    ∃ y : L, ∀ x : L, ∃ b : GU σ n, IsUnipU b ∧
      sR σ hσ a h * uR σ hσ a h x * v = b * (sR σ hσ a h * uR σ hσ a h (x + y)) := by
  first | exact @GlobalTheory.CompanionTheory.SwapRoot.Unip.sR_uR_mul_unip | exact GlobalTheory.CompanionTheory.SwapRoot.Unip.sR_uR_mul_unip | (intros; apply GlobalTheory.CompanionTheory.SwapRoot.Unip.sR_uR_mul_unip <;> assumption)
end
