module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Mathlib.Analysis.Matrix.LDL
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle126
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KTypesAboveOfDsClass
public import Formalism.HermitianLattices.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteUnimodularPlaneSplitAlongVector
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open Matrix Finset Formalism.MainNotions.S
open scoped ComplexOrder

namespace GlobalTheory.Dec

private lemma blockTriangular_toDual_of_isLo {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : IsLo b) :
    b.BlockTriangular OrderDual.toDual :=
  fun i j hij => hb i j (OrderDual.toDual_lt_toDual.mp hij)

private lemma isLo_of_blockTriangular_toDual {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ}
    (hb : b.BlockTriangular OrderDual.toDual) : IsLo b :=
  fun _ _ hij => hb (OrderDual.toDual_lt_toDual.mpr hij)

theorem exists_isLo_mul_conjTranspose {n : ℕ} {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    ∃ b : Matrix (Fin n) (Fin n) ℂ, IsLo b ∧ x = b * bᴴ := by
  classical

  have hLi : (LDL.lowerInv hx).BlockTriangular OrderDual.toDual :=
    LDL.isLowerTriangular_lowerInv hx
  have hL : (LDL.lower hx).BlockTriangular OrderDual.toDual :=
    Matrix.blockTriangular_inv_of_blockTriangular hLi

  have hD : (LDL.diag hx).PosDef := by
    rw [LDL.diag_eq_lowerInv_conj]
    refine hx.mul_mul_conjTranspose_same ?_
    intro v w hvw
    have h := congrArg (fun u => u ᵥ* (LDL.lowerInv hx)⁻¹) hvw
    simpa [Matrix.vecMul_vecMul, Matrix.mul_inv_of_invertible] using h
  have hd : ∀ i, 0 < LDL.diagEntries hx i := fun i => by
    simpa [LDL.diag] using hD.diag_pos (i := i)
  let s : Fin n → ℂ := fun i => ((Real.sqrt (LDL.diagEntries hx i).re : ℝ) : ℂ)
  have hs : ∀ i, s i * star (s i) = LDL.diagEntries hx i := fun i => by
    obtain ⟨hre, him⟩ := Complex.pos_iff.mp (hd i)
    have hsq := Real.mul_self_sqrt hre.le
    apply Complex.ext
    · simp [s, Complex.mul_re, hsq]
    · simp [s, Complex.mul_im, ← him]
  refine ⟨LDL.lower hx * Matrix.diagonal s,
    isLo_of_blockTriangular_toDual (hL.mul (Matrix.blockTriangular_diagonal s)), ?_⟩
  have hDs : LDL.diag hx = Matrix.diagonal s * (Matrix.diagonal s)ᴴ := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    unfold LDL.diag
    congr 1
    funext i
    exact (hs i).symm
  conv_lhs => rw [← LDL.lower_conj_diag hx, hDs]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem one_mem_Omega_leadMinor (n : ℕ) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Omega n := by
  intro i
  simp [leadMinor, Matrix.submatrix_one _ (Fin.castLE_injective _)]

theorem diag_ne_zero_of_posDef_mul_conjTranspose {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : IsLo b)
    (hx : (b * bᴴ).PosDef) (l : Fin n) : b l l ≠ 0 := by
  classical
  have hdet : (b * bᴴ).det ≠ 0 := hx.det_pos.ne'
  have hb' : b.det ≠ 0 := fun h => hdet (by rw [Matrix.det_mul, h, zero_mul])
  rw [Matrix.det_of_isLowerTriangular b (blockTriangular_toDual_of_isLo hb)] at hb'
  exact Finset.prod_ne_zero_iff.mp hb' l (Finset.mem_univ l)

private lemma phi_mul_conjTranspose_of_isLo (hT : PhiTri) {n : ℕ} (lam : Fin n → ℝ)
    {b : Matrix (Fin n) (Fin n) ℂ} (hb : IsLo b) (hd : ∀ l, b l l ≠ 0) :
    b * bᴴ ∈ Omega n ∧ Phi lam (b * bᴴ) = ((∏ l, ‖b l l‖ ^ (-(2 * muInt lam l)) : ℝ) : ℂ) := by
  have hup : IsUp bᴴ := fun i j hji => by
    simp [Matrix.conjTranspose_apply, hb j i hji]
  have h := hT n lam b 1 bᴴ hb hup
    (fun l => ⟨hd l, by simpa [Matrix.conjTranspose_apply] using hd l⟩) (one_mem_Omega_leadMinor n)
  rw [Matrix.mul_one] at h
  refine ⟨h.1, ?_⟩
  rw [h.2, Phi_at_one, mul_one, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj', Complex.ofReal_zpow,
    ← zpow_natCast, ← _root_.zpow_mul]
  congr 1
  push_cast
  ring

theorem phiPos_of_phiTri (hT : PhiTri) : PhiPos := by
  intro n lam x hx
  obtain ⟨b, hb, rfl⟩ := exists_isLo_mul_conjTranspose hx
  have hd := fun l => diag_ne_zero_of_posDef_mul_conjTranspose hb hx l
  obtain ⟨hΩ, hΦ⟩ := phi_mul_conjTranspose_of_isLo hT lam hb hd
  refine ⟨hΩ, ?_, ⟨b, hb, rfl⟩, fun b' hb' hx' => ?_⟩
  · rw [hΦ, Complex.zero_lt_real]
    exact Finset.prod_pos fun l _ => zpow_pos (norm_pos_iff.mpr (hd l)) _
  · have hx2 : (b' * b'ᴴ).PosDef := hx' ▸ hx
    rw [hx']
    exact (phi_mul_conjTranspose_of_isLo hT lam hb'
      (fun l => diag_ne_zero_of_posDef_mul_conjTranspose hb' hx2 l)).2

theorem phiPos : PhiPos := phiPos_of_phiTri GlobalTheory.PhiTriangular.phiTri

end GlobalTheory.Dec
end

section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.ClassificationConsequences

open GlobalTheory.LowestKTypeDetermines

variable {n : ℕ} {ε : Fin n → Bool} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {τ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}

theorem mul_mem_UJset {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε) :
    a * b ∈ UJset ε := by
  have ha' : aᴴ * Jm ε * a = Jm ε := ha
  have hb' : bᴴ * Jm ε * b = Jm ε := hb
  show (a * b)ᴴ * Jm ε * (a * b) = Jm ε
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Jm ε * (a * b) = bᴴ * (aᴴ * Jm ε * a) * b := by simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [ha', hb']

theorem isSqIntIrr_of_uEquiv (he : UEquiv ε σ τ) (h : IsSqIntIrr ε τ) : IsSqIntIrr ε σ := by
  obtain ⟨T, hT⟩ := he
  obtain ⟨hc, hn, ⟨⟨h1, hmul⟩, hiso, hcont⟩, hirr, hsq⟩ := h

  have hσ : ∀ g ∈ UJset ε, ∀ v, σ g v = T.symm (τ g (T v)) := by
    intro g hg v
    rw [← hT g hg v, LinearIsometryEquiv.symm_apply_apply]
  have one_mem : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
    show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * 1 = Jm ε
    simp
  refine ⟨?_, ?_, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · haveI := hc
    exact T.toIsometryEquiv.completeSpace
  · haveI := hn
    exact T.toLinearEquiv.toEquiv.nontrivial
  · ext v
    rw [hσ 1 one_mem v, h1]
    simp
  · intro a ha b hb
    ext v
    rw [hσ _ (mul_mem_UJset ha hb), hmul a ha b hb, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, hσ a ha, hσ b hb, LinearIsometryEquiv.apply_symm_apply]
  · intro g hg v
    rw [hσ g hg v, LinearIsometryEquiv.norm_map, hiso g hg, LinearIsometryEquiv.norm_map]
  · intro v
    have hc' : ContinuousOn (fun g => T.symm (τ g (T v))) (UJset ε) :=
      T.symm.continuous.comp_continuousOn (hcont (T v))
    exact hc'.congr (fun g hg => hσ g hg v)
  ·
    intro S hS hst
    let S' : Submodule ℂ H' := S.comap (T.symm.toLinearEquiv : H' →ₗ[ℂ] H)
    have mem' : ∀ w, w ∈ S' ↔ T.symm w ∈ S := fun w => Iff.rfl
    have hcl : IsClosed (S' : Set H') := hS.preimage T.symm.continuous
    have hst' : ∀ g ∈ UJset ε, ∀ w ∈ S', τ g w ∈ S' := by
      intro g hg w hw
      rw [mem'] at hw ⊢
      rw [symm_inter T hT g hg w]
      exact hst g hg _ hw
    rcases hirr S' hcl hst' with h0 | h0
    · left
      rw [Submodule.eq_bot_iff]
      intro v hv
      have hTv : T v ∈ S' := by
        rw [mem', LinearIsometryEquiv.symm_apply_apply]
        exact hv
      rw [h0, Submodule.mem_bot] at hTv
      exact (LinearIsometryEquiv.map_eq_zero_iff T).mp hTv
    · right
      rw [Submodule.eq_top_iff']
      intro v
      have hTv : T v ∈ S' := by
        rw [h0]
        exact Submodule.mem_top
      rw [mem', LinearIsometryEquiv.symm_apply_apply] at hTv
      exact hTv
  ·
    intro v w
    have heq : coefOn (ε := ε) σ v w = coefOn (ε := ε) τ (T v) (T w) := by
      funext g
      have hg : umat g ∈ UJset ε := g.2
      simp only [coefOn]
      rw [← hT _ hg v, LinearIsometryEquiv.inner_map_map]
    rw [heq]
    exact hsq (T v) (T w)

theorem isDS_of_uEquiv {lam : Fin n → ℝ} (he : UEquiv ε σ τ) (h : IsDS ε lam τ) : IsDS ε lam σ := by
  obtain ⟨c1, c2, c3, c4, c5⟩ :=
    isSqIntIrr_of_uEquiv he ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩
  obtain ⟨T, hT⟩ := he
  refine ⟨c1, c2, c3, c4, c5, ?_, ?_⟩
  · exact exists_ktype_of_uEquiv (uEquiv_symm ⟨T, hT⟩) h.2.2.2.2.2.1
  · intro μ S hS
    exact h.2.2.2.2.2.2 μ _ (ktype_transfer T hT hS)

theorem isKFin_transfer (T : H ≃ₗᵢ[ℂ] H') (h : ∀ g ∈ UJset ε, ∀ v, T (σ g v) = τ g (T v)) {v : H}
    (hv : IsKFin ε σ v) : IsKFin ε τ (T v) := by
  obtain ⟨S, hfin, hvS, hst⟩ := hv
  refine ⟨S.map (T.toLinearEquiv : H →ₗ[ℂ] H'), ?_, Submodule.mem_map_of_mem hvS, ?_⟩
  · haveI := hfin
    infer_instance
  · intro g hg w hw
    obtain ⟨u, hu, hwu⟩ := Submodule.mem_map.mp hw
    have hw' : w = T u := hwu.symm
    subst hw'
    rw [← h g (Kset_sub hg) u]
    exact Submodule.mem_map_of_mem (hst g hg u hu)

theorem isZEigen_congr {χ : Fin n → ℂ} {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : ∀ g, inUJ ε g → f g = f' g) (hf : IsZEigen ε χ f') : IsZEigen ε χ f := by
  obtain ⟨hsm, heig⟩ := hf
  refine ⟨?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hsm g₀ hg₀
    exact ⟨U, F, hU, hgU, hF, fun g hgU' hg => (h g hg).trans (hfF g hgU' hg)⟩
  · intro m g hg

    have hgel : gelf ε m f g = gelf ε m f' g := by
      simp only [gelf]
      exact Finset.sum_congr rfl (fun a _ => Eword_congr ε h _ g hg)
    rw [hgel, heig m g hg, h g hg]

theorem hasInfChar_of_uEquiv {χ : Fin n → ℂ} (he : UEquiv ε σ τ) (h : HasInfChar ε χ τ) :
    HasInfChar ε χ σ := by
  obtain ⟨T, hT⟩ := he
  intro v w hv hw
  have hz := h (T v) (T w) (isKFin_transfer T hT hv) (isKFin_transfer T hT hw)
  refine isZEigen_congr (fun g hg => ?_) hz
  show ⟪w, σ g v⟫_ℂ = ⟪T w, τ g (T v)⟫_ℂ
  rw [← hT g hg v, LinearIsometryEquiv.inner_map_map]

theorem dsExhaust_of_dsClass (h : DSClass) : DSExhaust := by
  intro n ε H _ _ σ hσ
  obtain ⟨G, i1, i2, π, hπ, hcl⟩ := h n
  obtain ⟨s, mu, hmu, hs, he⟩ := hcl ε H σ hσ
  exact ⟨s, mu, hmu, hs, isDS_of_uEquiv he (isDS_of_isHCDS hmu (hπ (ε ∘ s) mu hmu))⟩

theorem dsInfChar_of_dsClass (h : DSClass) : DSInfChar := by
  intro n ε lam H _ _ σ hl hσ
  obtain ⟨G, i1, i2, π, hπ, huniq⟩ := exists_model h ε hl
  exact hasInfChar_of_uEquiv (huniq H σ hσ) hπ.2.1

theorem strictLow_of_dsClass (h : DSClass) : StrictLow := by
  intro n ε lam hl H _ _ _ σ hσ
  obtain ⟨S0, hS0⟩ := hσ.2.2.2.2.2.1
  refine ⟨?_, ?_⟩
  ·
    have hset : {S : Submodule ℂ H | IsKTypeOf ε σ (lowK ε lam) S} = {S0} := by
      ext S
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · intro hS
        exact lowKMultOne_of_dsClass h n ε lam H σ hl hσ S S0 hS hS0
      · rintro rfl
        exact hS0
    have hsub : lowKSub ε lam σ = S0 := by
      show sSup {S : Submodule ℂ H | IsKTypeOf ε σ (lowK ε lam) S} = S0
      rw [hset, sSup_singleton]
    rw [hsub]
    exact hS0
  ·
    intro μ S hS hne
    obtain ⟨c, hc, hμ⟩ := kTypesAbove_of_dsClass h n ε lam H σ hl hσ μ S hS
    have hQ0 : (∑ a, ∑ b, (c a b : ℝ) • root a b) ≠ 0 := by
      intro h0
      apply hne
      rw [hμ, h0, add_zero]
    have hx : Antitone (lam + Formalism.QuantumDeterminants.rhoStd n) := (strictAnti_add_rho hl.1).antitone
    have hcone := nsq_add_cone hx hc
    have hpos : 0 < nsq (∑ a, ∑ b, (c a b : ℝ) • root a b) := by
      rcases (nsq_nonneg (∑ a, ∑ b, (c a b : ℝ) • root a b)).lt_or_eq with hp | hp
      · exact hp
      · exact absurd (eq_zero_of_nsq hp.symm.le) hQ0
    have e1 : vNormSq ε (lowK ε lam) = nsq (lam + Formalism.QuantumDeterminants.rhoStd n) := by
      show nsq (lowK ε lam + (2 : ℝ) • rhoC ε) = _
      rw [lowK_add]
    have e2 : vNormSq ε μ = nsq (lam + Formalism.QuantumDeterminants.rhoStd n + ∑ a, ∑ b, (c a b : ℝ) • root a b) := by
      show nsq (μ + (2 : ℝ) • rhoC ε) = _
      rw [hμ, add_right_comm (lowK ε lam) _ ((2 : ℝ) • rhoC ε), lowK_add]
    rw [e1, e2]
    linarith

theorem consequences_of_dsClass :
    DSClass → DSExists ∧ DSExhaust ∧ DSUnique ∧ DSInfChar ∧ LowKMultOne ∧ KTypesAbove ∧ StrictLow := by
  intro h
  exact ⟨dsExists_of_dsClass h, dsExhaust_of_dsClass h, dsUnique_of_dsClass h, dsInfChar_of_dsClass h,
    lowKMultOne_of_dsClass h, kTypesAbove_of_dsClass h, strictLow_of_dsClass h⟩

end GlobalTheory.ClassificationConsequences
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
namespace GlobalTheory.PlaneSplit

private theorem planeSplit_of_lattice : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (J : Matrix (Fin 2) (Fin 2) E), Jᴴ = J → (∀ (φ : E →+* ℂ) (y : Fin 2 → E), y ≠ 0 → 0 < (φ (star y ⬝ᵥ (J *ᵥ y))).re) → ∀ Λ : Submodule (𝓞 E) (Fin 2 → E), Submodule.IsLattice E Λ → (∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) → ∀ u ∈ Λ, u ≠ 0 → ∀ ρ : ℝ, (∀ φ : E →+* ℂ, (φ (star u ⬝ᵥ (J *ᵥ u))).re ≤ ρ) → ∃ (γ : GL (Fin 2) E) (β₁ β₂ : E) (N₁ N₂ : Submodule (𝓞 E) E) (𝔫 : Ideal (𝓞 E)), (γ : Matrix (Fin 2) (Fin 2) E)ᴴ * J * (γ : Matrix (Fin 2) (Fin 2) E) = Matrix.diagonal ![β₁, β₂] ∧ star β₁ = β₁ ∧ star β₂ = β₂ ∧ (∀ φ : E →+* ℂ, 0 < (φ β₁).re ∧ 0 < (φ β₂).re) ∧ Submodule.IsFullLattice E N₁ ∧ Submodule.IsFullLattice E N₂ ∧ (∀ t, t ∈ N₁ ↔ (γ : Matrix (Fin 2) (Fin 2) E) *ᵥ ![t, 0] ∈ Λ) ∧ (∀ t, t ∈ N₂ ↔ (γ : Matrix (Fin 2) (Fin 2) E) *ᵥ ![0, t] ∈ Λ) ∧ Submodule.span (𝓞 E) {t | ∃ x ∈ N₁, ∃ y ∈ N₁, t = star x * β₁ * y} = Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫 ∧ Submodule.span (𝓞 E) {t | ∃ x ∈ N₂, ∃ y ∈ N₂, t = star x * β₂ * y} = Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫 ∧ 𝔫 ≠ ⊥ ∧ 𝔫 = Ideal.span {t | t ∈ 𝔫 ∧ star (t : E) = t} ∧ (Ideal.absNorm 𝔫 : ℝ) ≤ ρ ^ (2 * Formalism.HermitianLatticesTheory.fDeg E) := by
  intro E _ _ _ hE J hJ hpos Λ hΛ hdual u hu hu0 ρ hρ
  have hne : ∀ y : Fin 2 → E, y ≠ 0 → star y ⬝ᵥ (J *ᵥ y) ≠ 0 := by
    intro y hy h
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have := hpos φ y hy
    rw [h] at this
    simp at this
  set v := star u ᵥ* J with hv
  let w : Fin 2 → E := ![-v 1, v 0]
  have huw : star u ⬝ᵥ (J *ᵥ w) = 0 := by
    rw [dotProduct_mulVec, ← hv]; simp [w, dotProduct, Fin.sum_univ_two]; ring
  have hwu : star w ⬝ᵥ (J *ᵥ u) = 0 := by rw [← herm_star J hJ, huw, star_zero]
  set β₁ := star u ⬝ᵥ (J *ᵥ u) with hβ₁
  set β₂ := star w ⬝ᵥ (J *ᵥ w) with hβ₂
  have h10 : β₁ ≠ 0 := hne u hu0
  have hb1 : β₁ = v 0 * u 0 + v 1 * u 1 := by
    rw [hβ₁, dotProduct_mulVec, ← hv]; simp [dotProduct, Fin.sum_univ_two]
  have hw0 : w ≠ 0 := by
    intro h
    have a0 := congrFun h 0
    have a1 := congrFun h 1
    simp [w] at a0 a1
    exact h10 (by rw [hb1, a0, a1]; ring)
  have h20 : β₂ ≠ 0 := hne w hw0
  have h1 : star β₁ = β₁ := herm_star J hJ u u
  have h2 : star β₂ = β₂ := herm_star J hJ w w
  let G : Matrix (Fin 2) (Fin 2) E := Matrix.of fun i j => ![u, w] j i
  have hG : G.det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simp only [G, w, Matrix.of_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    intro h; apply h10; rw [hb1, ← h]; ring
  have hGv : ∀ a b : E, G *ᵥ ![a, b] = a • u + b • w := by
    intro a b; ext i; simp [G, mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
  have hGJ : Gᴴ * J * G = Matrix.diagonal ![β₁, β₂] := by
    have : ∀ i j, (Gᴴ * J * G) i j = star (![u, w] i) ⬝ᵥ (J *ᵥ (![u, w] j)) := by
      intro i j
      simp [G, Matrix.mul_apply, mulVec, dotProduct, Fin.sum_univ_two]; ring
    ext i j
    rw [this]
    fin_cases i <;> fin_cases j
    exacts [rfl, huw, hwu, rfl]
  let f : (E × E) →ₗ[E] (Fin 2 → E) :=
    (LinearMap.toSpanSingleton E _ u).coprod (LinearMap.toSpanSingleton E _ w)
  have hf : ∀ x : E × E, f x = x.1 • u + x.2 • w := fun x => rfl
  have hpair : ∀ x y : E × E, star (f y) ⬝ᵥ (J *ᵥ f x) = star y.1 * β₁ * x.1 + star y.2 * β₂ * x.2 := by
    intro x y
    rw [hf, hf]
    simp only [star_add, star_smul, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, huw, hwu, ← hβ₁, ← hβ₂, smul_eq_mul]
    ring
  have hinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have a0 := hpair x (1, 0)
    have a1 := hpair x (0, 1)
    simp [hx, h10, h20] at a0 a1
    exact Prod.ext a0 a1
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
  let L : Submodule (𝓞 E) (E × E) := Λ.comap (f.restrictScalars (𝓞 E))
  have hLm : ∀ x, x ∈ L ↔ f x ∈ Λ := fun x => Iff.rfl
  have hLfg : L.FG := by
    apply Submodule.fg_of_fg_map_injective (f.restrictScalars (𝓞 E)) hinj
    rw [Submodule.map_comap_eq_of_surjective (f := f.restrictScalars (𝓞 E)) hsurj]
    exact hΛ.fg
  have hu1 : ((1, 0) : E × E) ∈ L := by rw [hLm, hf]; simpa using hu
  have hq : ∃ x ∈ L, x.2 ≠ 0 := by
    by_contra h
    push Not at h
    have hwmem : f (0, 1) ∈ Λ := by
      apply (hdual _).2
      intro y hy
      obtain ⟨z, rfl⟩ := hsurj y
      have hz : z.2 = 0 := h z hy
      rw [hpair]
      simp [hz]
    have := h (0, 1) hwmem
    simp at this
  have hL : ∀ x, x ∈ L ↔ ∀ y ∈ L, IsIntegral ℤ (star y.1 * β₁ * x.1 + star y.2 * β₂ * x.2) := by
    intro x
    rw [hLm, hdual]
    constructor
    · intro h y hy
      rw [← hpair, ← mem_range_iff]; exact h _ hy
    · intro h y hy
      obtain ⟨y, rfl⟩ := hsurj y
      rw [mem_range_iff, hpair]; exact h y hy
  obtain ⟨A, B, 𝔫, hA, hB, hA', hB', hS, hT, hfix⟩ :=
    diag_split β₁ β₂ h1 h2 h10 h20 L hLfg ⟨_, hu1, one_ne_zero⟩ hq hL
  have hβn : β₁ ∈ Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫 := by
    rw [← hS]
    exact Submodule.subset_span ⟨1, (hA' 1).2 hu1, 1, (hA' 1).2 hu1, by simp⟩
  obtain ⟨b, hb, hbβ⟩ := hβn
  have hbβ' : (b : E) = β₁ := hbβ
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact h10 (by rw [← hbβ']; rfl)
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero G hG, β₁, β₂, A, B, 𝔫, hGJ, h1, h2,
    fun φ => ⟨hpos φ u hu0, hpos φ w hw0⟩, hA, hB, fun t => ?_, fun t => ?_, hS, hT, ?_, hfix, ?_⟩
  · rw [hA', hLm, hf]
    change _ ↔ G *ᵥ _ ∈ Λ
    rw [hGv]
  · rw [hB', hLm, hf]
    change _ ↔ G *ᵥ _ ∈ Λ
    rw [hGv]
  · rintro rfl
    exact hb0 hb
  · refine absNorm_le hE.1 𝔫 b hb hb0 ρ fun φ => ?_
    rw [hbβ']
    have him : (φ β₁).im = 0 := by
      have := hE.2.1 φ β₁
      rw [h1] at this
      exact Complex.conj_eq_iff_im.1 this.symm
    rw [← Complex.abs_re_eq_norm.2 him, abs_of_pos (hpos φ u hu0)]
    exact hρ φ


end GlobalTheory.PlaneSplit


theorem _root_.GlobalTheory.T.definiteUnimodularPlane_split_along_vector : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (J : Matrix (Fin 2) (Fin 2) E), Jᴴ = J → (∀ (φ : E →+* ℂ) (y : Fin 2 → E), y ≠ 0 → 0 < (φ (star y ⬝ᵥ (J *ᵥ y))).re) → ∀ Λ : Submodule (𝓞 E) (Fin 2 → E), Submodule.IsLattice E Λ → (∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) → ∀ u ∈ Λ, u ≠ 0 → ∀ ρ : ℝ, (∀ φ : E →+* ℂ, (φ (star u ⬝ᵥ (J *ᵥ u))).re ≤ ρ) → ∃ (γ : GL (Fin 2) E) (β₁ β₂ : E) (N₁ N₂ : Submodule (𝓞 E) E) (𝔫 : Ideal (𝓞 E)), (γ : Matrix (Fin 2) (Fin 2) E)ᴴ * J * (γ : Matrix (Fin 2) (Fin 2) E) = Matrix.diagonal ![β₁, β₂] ∧ star β₁ = β₁ ∧ star β₂ = β₂ ∧ (∀ φ : E →+* ℂ, 0 < (φ β₁).re ∧ 0 < (φ β₂).re) ∧ Submodule.IsLattice E N₁ ∧ Submodule.IsLattice E N₂ ∧ (∀ t, t ∈ N₁ ↔ (γ : Matrix (Fin 2) (Fin 2) E) *ᵥ ![t, 0] ∈ Λ) ∧ (∀ t, t ∈ N₂ ↔ (γ : Matrix (Fin 2) (Fin 2) E) *ᵥ ![0, t] ∈ Λ) ∧ Submodule.span (𝓞 E) {t | ∃ x ∈ N₁, ∃ y ∈ N₁, t = star x * β₁ * y} = Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫 ∧ Submodule.span (𝓞 E) {t | ∃ x ∈ N₂, ∃ y ∈ N₂, t = star x * β₂ * y} = Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫 ∧ 𝔫 ≠ ⊥ ∧ 𝔫 = Ideal.span {t | t ∈ 𝔫 ∧ star (t : E) = t} ∧ (Ideal.absNorm 𝔫 : ℝ) ≤ ρ ^ (2 * Formalism.HermitianLatticesTheory.fDeg E) := by
  intro E _ _ _ hE J hJ hpos Λ hΛ hdual u hu hu0 ρ hρ
  obtain ⟨γ, β₁, β₂, N₁, N₂, 𝔫, hγ, hβ₁, hβ₂, hpos', hN₁, hN₂, hrest⟩ :=
    GlobalTheory.PlaneSplit.planeSplit_of_lattice E hE J hJ hpos Λ hΛ hdual u hu hu0 ρ hρ
  exact ⟨γ, β₁, β₂, N₁, N₂, 𝔫, hγ, hβ₁, hβ₂, hpos', hN₁.toIsLattice, hN₂.toIsLattice, hrest⟩
end
