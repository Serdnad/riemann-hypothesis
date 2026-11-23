module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeAntidiagFixed
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle008
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle387
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.InstCommRingBcris
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import GroundTheory.PAdicHodge.UnramifiedClosure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle386
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveBot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineSmoothFormsBijective
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.lift_levelP_alt₂
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.IsStrictDom
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle223
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle214
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot

namespace GlobalTheory.CompanionTheory.SwapFactor

section Local
variable {L : Type} [Field L]

def betaU (x : L) (hx : x ≠ 0) : GL (Fin 2) L where
  val := !![-x⁻¹, 1; 0, x]
  inv := !![-x, 1; 0, x⁻¹]
  val_inv := by
    ext p r; fin_cases p <;> fin_cases r <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hx]
  inv_val := by
    ext p r; fin_cases p <;> fin_cases r <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hx]

theorem wU_mul_nU (x : L) (hx : x ≠ 0) :
    wU L * nU x = betaU x hx * (wU L * nU x⁻¹ * wU L) := by
  apply Units.ext
  ext p r
  fin_cases p <;> fin_cases r <;>
    simp [betaU, wU, nU, w2, Matrix.mul_apply, Fin.sum_univ_two, hx]

theorem partner_betaU_lower (σ : L →+* L) (x : L) (hx : x ≠ 0) : partner σ (betaU x hx) 1 0 = 0 := by
  have : ((betaU x hx)⁻¹ : GL (Fin 2) L).val = !![-x, 1; 0, x⁻¹] := rfl
  have hw : ∀ M : Matrix (Fin 2) (Fin 2) L, (w2 L * M * w2 L) 1 0 = M 0 1 := fun M => by
    simp [w2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  rw [partner, hw, this]
  simp [cT]

theorem arith (u v Q : ℂ) (hQ : Q ≠ 0) (o N : ℤ) :
    u ^ (-o) * Q ^ (-(-o) * N) * (v ^ o * Q ^ (-o * (N - 2))) = ((u / v) / Q ^ 2) ^ (-o) := by
  have h2 : (Q ^ 2) ^ (-o) = Q ^ (-(2 * o)) := by
    rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
  have h3 : Q ^ (-(-o) * N) * Q ^ (-o * (N - 2)) = Q ^ (2 * o) := by
    rw [← zpow_add₀ hQ]; congr 1; ring
  have h4 : v ^ o = (v ^ (-o))⁻¹ := by rw [zpow_neg, inv_inv]
  rw [div_zpow, div_zpow, h2, zpow_neg Q (2 * o)]
  calc _ = u ^ (-o) * (v ^ (-o))⁻¹ * (Q ^ (-(-o) * N) * Q ^ (-o * (N - 2))) := by rw [h4]; ring
    _ = _ := by rw [h3]; simp [div_eq_mul_inv]

end Local

section Root
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {σ : L →+* L}

theorem ordL_neg' (x : L) (hx : x ≠ 0) : ordL (-x) = ordL x := by
  have h1 := v_eq_exp' (neg_ne_zero.2 hx)
  rw [Valuation.map_neg, v_eq_exp' hx] at h1
  have := WithZero.exp_injective h1
  omega

theorem ordL_one' : ordL (1 : L) = 0 := by simp [ordL]; rfl

theorem isBorel_root (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L) (hx : x ≠ 0) :
    IsBorelU (rootHom σ hσ a h (betaU x hx)) := by
  intro i j hji
  rw [rootHom_val]
  by_cases hI : (∃ p, i = cI n a h p) ∧ ∃ r, j = cI n a h r
  · obtain ⟨⟨p, rfl⟩, r, rfl⟩ := hI
    rw [blockM_cI]
    have hlt : (cI n a h r : ℕ) < (cI n a h p : ℕ) := hji
    simp only [cI] at hlt
    have hp : p = 1 := Fin.ext (by have := p.2; simp only [Fin.val_one]; omega)
    have hr : r = 0 := Fin.ext (by have := r.2; simp only [Fin.val_zero]; omega)
    subst hp hr
    rfl
  by_cases hJ : (∃ p, i = cJ n a h p) ∧ ∃ r, j = cJ n a h r
  · obtain ⟨⟨p, rfl⟩, r, rfl⟩ := hJ
    rw [blockM_cJ]
    have hlt : (cJ n a h r : ℕ) < (cJ n a h p : ℕ) := hji
    simp only [cJ] at hlt
    have hp : p = 1 := Fin.ext (by have := p.2; simp only [Fin.val_one]; omega)
    have hr : r = 0 := Fin.ext (by have := r.2; simp only [Fin.val_zero]; omega)
    subst hp hr
    exact partner_betaU_lower σ x hx
  rw [blockM_out]
  · exact Matrix.one_apply_ne (ne_of_gt hji)
  · by_contra hc
    push_neg at hc
    exact hI ⟨by simpa [eq_comm] using hc.1, by simpa using hc.2⟩
  · by_contra hc
    push_neg at hc
    exact hJ ⟨by simpa using hc.1, by simpa using hc.2⟩

theorem diag_a (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L) (hx : x ≠ 0) (hk : a < n) :
    (((rootHom σ hσ a h (betaU x hx) : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) ⟨a, hk⟩ ⟨a, hk⟩ = -x⁻¹ := by
  have e : (⟨a, hk⟩ : Fin n) = cI n a h 0 := Fin.ext (by simp [cI])
  rw [e, rootHom_val, blockM_cI]
  rfl

theorem root_hom_diag_entry_eq (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L) (hx : x ≠ 0) (hk : a + 1 < n) :
    (((rootHom σ hσ a h (betaU x hx) : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) ⟨a + 1, hk⟩ ⟨a + 1, hk⟩ = x := by
  have e : (⟨a + 1, hk⟩ : Fin n) = cI n a h 1 := Fin.ext (by simp [cI])
  rw [e, rootHom_val, blockM_cI]
  rfl

theorem diag_other (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L) (hx : x ≠ 0) (k : Fin n)
    (hk : k.val < n / 2) (h1 : k.val ≠ a) (h2 : k.val ≠ a + 1) :
    (((rootHom σ hσ a h (betaU x hx) : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) k k = 1 := by
  rw [rootHom_val, blockM_out]
  · exact Matrix.one_apply_eq k
  · left
    intro p e
    have := congrArg Fin.val e
    have hp := p.2
    simp only [cI] at this
    omega
  · left
    intro p e
    have := congrArg Fin.val e
    have hp := p.2
    simp only [cJ] at this
    omega

end Root

theorem sR_uR_factor : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ) (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) (χ : Fin (n / 2) → ℂˣ) (i j : Fin (n / 2)), i.val = a → j.val = a + 1 → ∀ x : L, x ≠ 0 →
    ∃ b : GU σ n, IsBorelU b ∧
      chiDeltaU q (fun k => (χ k : ℂ)) b = (((χ i : ℂ) / (χ j : ℂ)) / (q : ℂ) ^ 2) ^ (-ordL x) ∧
      sR σ hU.1 a h * uR σ hU.1 a h x = b * (sR σ hU.1 a h * uR σ hU.1 a h x⁻¹ * sR σ hU.1 a h) := by
  intro L _ _ ϖ σ q n hU a h χ i j hi hj x hx
  have hq : (q : ℂ) ≠ 0 := by
    have : 2 ≤ q := hU.2.2.2.2.2.1
    exact Nat.cast_ne_zero.2 (by omega)
  refine ⟨rootHom σ hU.1 a h (betaU x hx), isBorel_root hU.1 a h x hx, ?_, ?_⟩
  · have hij : i ≠ j := fun e => by
      have := congrArg Fin.val e
      omega
    have ha : a < n := by omega
    have ha1 : a + 1 < n := by omega
    have hin : i.val < n := by omega
    have hjn : j.val < n := by omega
    unfold chiDeltaU
    rw [Finset.prod_eq_mul i j hij ?_ (by simp) (by simp)]
    · rw [dite_eq_left hin, dite_eq_left hjn]
      have ei : (⟨i.val, hin⟩ : Fin n) = ⟨a, ha⟩ := Fin.ext hi
      have ej : (⟨j.val, hjn⟩ : Fin n) = ⟨a + 1, ha1⟩ := Fin.ext hj
      rw [ei, ej, diag_a, root_hom_diag_entry_eq, ordL_neg' _ (inv_ne_zero hx), ordL_inv' hx, hi, hj]
      have hN : ((n : ℤ) - 1 - 2 * ((a + 1 : ℕ) : ℤ)) = ((n : ℤ) - 1 - 2 * (a : ℤ)) - 2 := by
        push_cast; ring
      rw [hN]
      exact arith _ _ _ hq _ _
    · intro k _ hk
      have hkn : k.val < n := by omega
      rw [dite_eq_left hkn, diag_other hU.1 a h x hx ⟨k.val, hkn⟩ (by simpa using k.2)
        (fun e => hk.1 (Fin.ext (by simpa [hi] using e)))
        (fun e => hk.2 (Fin.ext (by simpa [hj] using e))), ordL_one']
      simp
  · simp only [sR, uR, ← map_mul]
    exact congrArg _ (wU_mul_nU x hx)

end GlobalTheory.CompanionTheory.SwapFactor

end
end

section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot

noncomputable section

namespace GlobalTheory.CompanionTheory.SwapRoot

section RootInt

variable {L : Type} [Field L]

theorem partner_nU (σ : L →+* L) (x : L) : partner σ (nU x) = !![1, -σ x; 0, 1] := by
  have hi : (((nU x)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = !![1, -x; 0, 1] := rfl
  have hc : cT σ (!![1, -x; 0, 1] : Matrix (Fin 2) (Fin 2) L) = !![1, 0; -σ x, 1] := by
    ext p r
    fin_cases p <;> fin_cases r <;> simp [cT]
  simp only [partner, hi, hc, w2]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp

variable [Valued L (WithZero (Multiplicative ℤ))]

theorem val_cM_conj_le_one {n : ℕ} (c : Fin 2 → Fin n) (P : Matrix (Fin 2) (Fin 2) L)
    (hP : ∀ p r, Valued.v (P p r) ≤ 1) (b d : Fin n) :
    Valued.v ((cM L c * P * (cM L c).transpose) b d) ≤ 1 := by
  rw [cM_conj_apply]
  refine Valuation.map_sum_le _ fun p _ => Valuation.map_sum_le _ fun r _ => ?_
  split_ifs
  · exact hP p r
  · rw [map_zero]; exact zero_le

theorem blockM_int {n : ℕ} (a : ℕ) (h : 2 * (a + 2) ≤ n) (X Y : Matrix (Fin 2) (Fin 2) L)
    (hX : ∀ p r, Valued.v ((X - 1) p r) ≤ 1) (hY : ∀ p r, Valued.v ((Y - 1) p r) ≤ 1) :
    Formalism.UG.P.fIwasawaInt (blockM a h X Y) := by
  intro b d
  simp only [blockM, Matrix.add_apply]
  exact Valuation.map_add_le _ (Valuation.map_add_le _ (Formalism.UG.P.fIwasawa_int_one b d)
    (val_cM_conj_le_one _ _ hX b d)) (val_cM_conj_le_one _ _ hY b d)

theorem val_unip_sub_one_le {y : L} (hy : Valued.v y ≤ 1) (p r : Fin 2) :
    Valued.v (((!![1, y; 0, 1] : Matrix (Fin 2) (Fin 2) L) - 1) p r) ≤ 1 := by
  fin_cases p <;> fin_cases r <;> simp [hy]

theorem uR_mem_KU : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ)
    (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L), Valued.v x ≤ 1 → uR σ hU.1 a h x ∈ KU σ n := by
  intro L _ _ ϖ σ q n hU a h x hx
  have hσv := hU.2.1
  have hI : Formalism.UG.P.fIwasawaInt (((uR σ hU.1 a h x : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    show Formalism.UG.P.fIwasawaInt (blockM a h (nU x : GL (Fin 2) L).val (partner σ (nU x)))
    rw [partner_nU]
    refine blockM_int a h _ _ (val_unip_sub_one_le hx) (val_unip_sub_one_le ?_)
    rw [Valuation.map_neg, hσv]
    exact hx
  have hK := Formalism.UG.P.fIwasawa_mk_mem_K σ hσv _ (Formalism.UG.P.fIwasawa_mem_un σ (uR σ hU.1 a h x)) hI
  have he : Formalism.UG.P.fIwasawaMk σ _ (Formalism.UG.P.fIwasawa_mem_un σ (uR σ hU.1 a h x)) = uR σ hU.1 a h x :=
    Subtype.ext (Units.ext (Formalism.UG.P.fIwasawa_mk_val σ _ _))
  rwa [he] at hK

end RootInt

end GlobalTheory.CompanionTheory.SwapRoot

end
end

section

noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot Matrix

namespace GlobalTheory.CompanionTheory.SwapRoot

variable {L : Type} [Field L]

theorem partner_wU (σ : L →+* L) : partner σ (wU L) = w2 L := by
  have hw : (((wU L)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = w2 L := rfl
  have hc : cT σ (w2 L) = w2 L := by
    delta cT w2
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  delta partner
  rw [hw, hc, weyl_mul_weyl, one_mul]

variable [Valued L (WithZero (Multiplicative ℤ))]

theorem cM_conj_int {n : ℕ} (c : Fin 2 → Fin n) (P : Matrix (Fin 2) (Fin 2) L)
    (hP : ∀ p r, Valued.v (P p r) ≤ 1) (b d : Fin n) :
    Valued.v ((cM L c * P * (cM L c)ᵀ) b d) ≤ 1 := by
  have hA : ∀ (x : Fin n) (p : Fin 2), Valued.v (cM L c x p) ≤ 1 := by
    intro x p
    show Valued.v (if x = c p then (1 : L) else 0) ≤ 1
    split_ifs <;> simp
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le (Valued.v : Valuation L (WithZero (Multiplicative ℤ))) fun r _ => ?_
  rw [Valuation.map_mul, Matrix.transpose_apply, Matrix.mul_apply]
  refine mul_le_one' ?_ (hA d r)
  refine Valuation.map_sum_le (Valued.v : Valuation L (WithZero (Multiplicative ℤ))) fun p _ => ?_
  rw [Valuation.map_mul]
  exact mul_le_one' (hA b p) (hP p r)

theorem weyl_sub_one_entries_integral (p r : Fin 2) : Valued.v ((w2 L - 1) p r) ≤ 1 := by
  delta w2
  fin_cases p <;> fin_cases r <;> simp [Matrix.one_apply]

theorem block_matrix_weyl_integral {n : ℕ} (a : ℕ) (h : 2 * (a + 2) ≤ n) :
    Formalism.UG.P.fIwasawaInt (blockM a h (w2 L) (w2 L)) := by
  delta blockM
  intro i j
  simp only [Matrix.add_apply]
  refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ (cM_conj_int _ _ weyl_sub_one_entries_integral i j))
    (cM_conj_int _ _ weyl_sub_one_entries_integral i j)
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem sR_mem_KU : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L)
    (σ : L →+* L) (q n : ℕ) (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n),
    sR σ hU.1 a h ∈ KU σ n := by
  intro L _ _ ϖ σ q n hU a h
  have hval : (((sR σ hU.1 a h : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      blockM a h (w2 L) (w2 L) := by
    show blockM a h (w2 L) (partner σ (wU L)) = _
    rw [partner_wU]
  have hwinv : (wU L)⁻¹ = wU L := Units.ext rfl
  have hginv : (sR σ hU.1 a h)⁻¹ = sR σ hU.1 a h := by
    show ((rootHom σ hU.1 a h) (wU L))⁻¹ = (rootHom σ hU.1 a h) (wU L)
    rw [← map_inv, hwinv]
  have hBB : blockM a h (w2 L) (w2 L) * blockM a h (w2 L) (w2 L) = 1 := by
    have h1 := ((sR σ hU.1 a h : GU σ n) : GL (Fin n) L).mul_inv
    rw [← Subgroup.coe_inv, hginv, hval] at h1
    exact h1
  have hint : ∀ i j, blockM a h (w2 L) (w2 L) i j ∈ intL L := fun i j => block_matrix_weyl_integral (L := L) a h i j
  let Bi : Matrix (Fin n) (Fin n) (intL L) := Matrix.of fun i j => ⟨blockM a h (w2 L) (w2 L) i j, hint i j⟩
  have hBi : ∀ i j, ((Bi * Bi) i j : L) = (blockM a h (w2 L) (w2 L) * blockM a h (w2 L) (w2 L)) i j := by
    intro i j
    simp [Bi, Matrix.mul_apply]
  have hy : Bi * Bi = 1 := by
    ext i j
    rw [hBi, hBB, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  show ((sR σ hU.1 a h : GU σ n) : GL (Fin n) L) ∈ GU σ n ⊓ (bc (intL L).subtype).range
  refine Subgroup.mem_inf.2 ⟨(sR σ hU.1 a h).2, ⟨⟨Bi, Bi, hy, hy⟩, ?_⟩⟩
  apply Units.ext
  rw [hval]
  ext i j
  rfl

end GlobalTheory.CompanionTheory.SwapRoot

end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

theorem _root_.GlobalTheory.T.kuenneth_product_proper_smooth : SiteLaws → MVBij → CovDesc → ZarAbs → AffOm → KunAff → ∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) [IsProper q] [Smooth q] [IsProper q'] [Smooth q'] (p₁ : P ⟶ X) (p₂ : P ⟶ X') (hP : IsPullback p₁ p₂ q q'), ∀ (h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T)) (h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q' ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T)), (hodgeXD q q' p₁ p₂ hP.w.symm).Kun (inU q ⊤) (inU q' ⊤) (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤)) h₁ h₂ := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.kun_left | exact GlobalTheory.CompanionTheory.KunGlue.kun_left | (intros; apply GlobalTheory.CompanionTheory.KunGlue.kun_left <;> assumption)
end

section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem _root_.GlobalTheory.T.ray_class_partial_zeta_integrality : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 𝔞 𝔟 𝔠 : Ideal (𝓞 F)) (J : Type) [Fintype J] (r : J → ℕ) (y : J → 𝓞 F) (v : ∀ j, Fin (r j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r y v → 𝔠.IsPrime → (Ideal.absNorm 𝔠).Prime → (∀ j i, v j i ∉ 𝔠 * 𝔟) → ∀ T : ℂ → ℂ, DifferentiableOn ℂ T {1}ᶜ → (∀ s : ℂ, 1 < s.re → HasSum (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} => (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) (T s)) → ∀ k : ℕ, 1 ≤ k → ∃ q : ℚ, T (1 - (k : ℂ)) = (q : ℂ) ∧ ∀ l : ℕ, l.Prime → l ≠ Ideal.absNorm 𝔠 → ¬ l ∣ Ideal.absNorm 𝔟 → 0 ≤ padicValRat l q := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Integrality.classTwist_value_int | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Integrality.classTwist_value_int | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Integrality.classTwist_value_int <;> assumption)
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical


theorem _root_.GlobalTheory.T.hodge_tate_character_weight : ∀ {l : ℕ} [Fact l.Prime] (L : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] ↥L],
    ((GroundTheory.PAdicHodge.cycloChar L) ''
        {σ : Gal(Om l/↥L) | ∀ w ∈ GroundTheory.PAdicHodge.unramifiedClosure l, σ w = w}).Infinite →
    ∀ (u : (Formalism.Per6.BdRp l)ˣ) (n : ℕ) (a : Gal(Om l/↥L) → ℚ_[l]),
    (∀ σ : Gal(Om l/↥L), σ • (GroundTheory.PAdicHodge.tBdR l ^ n * (u : Formalism.Per6.BdRp l)) =
      algebraMap ℚ_[l] (Formalism.Per6.BdRp l) (a σ) * (GroundTheory.PAdicHodge.tBdR l ^ n * (u : Formalism.Per6.BdRp l))) →
    (∀ σ : Gal(Om l/↥L), (∀ w ∈ GroundTheory.PAdicHodge.unramifiedClosure l, σ w = w) →
      a σ = (((GroundTheory.PAdicHodge.cycloChar L σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])) →
    n = 1 := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.eq_one_of_tpow_mul_unit_eigen | exact GlobalTheory.CompanionTheory.LTPer.eq_one_of_tpow_mul_unit_eigen | (intros; apply GlobalTheory.CompanionTheory.LTPer.eq_one_of_tpow_mul_unit_eigen <;> assumption)
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

theorem _root_.GlobalTheory.T.affine_smooth_forms_bijective : CrystallineSemistableComparison.Onto.AffOm → CrystallineSemistableComparison.Onto.OmNat → ∀ (K : Type) [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    [IsAffine X] [Smooth q] (a : ℕ),
    ∃ e : CrystallineSemistableComparison.Onto.Om K (CrystallineSemistableComparison.Onto.Sec q ⊤) a →ₗ[K] CrystallineSemistableComparison.Onto.HV q ⊤ a a, CrystallineSemistableComparison.Onto.IsOm q ⊤ a e ∧ Function.Bijective e := by
  first | exact @GlobalTheory.CompanionTheory.OmGlue.om_top | exact GlobalTheory.CompanionTheory.OmGlue.om_top | (intros; apply GlobalTheory.CompanionTheory.OmGlue.om_top <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.LFun PositivityTheory.JacquetShalikaLocal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SatakeBound

theorem jacquetShalikaBound_of_steps : ParameterUpperBound → liftZP_unit → ParameterAbsoluteValues → lift_levelP_alt₂ → G1 → G2 → G3 → G4 → GlobalTheory.Published.JacquetShalikaBound := by
  intro h10 h11 h11b h12 g1 g2 g3 g4 E _ _ _ a π hU w B hB α hα
  obtain ⟨L, rfl⟩ : ∃ L : List ℂˣ, (L : Multiset ℂˣ) = B := ⟨B.toList, Multiset.coe_toList B⟩
  have hcard : L.length = a := by simpa using hB.card
  subst hcard
  have hBz : (L : Multiset ℂˣ) = Finset.univ.val.map L.get := by rw [Fin.univ_val_map, List.ofFn_get]
  obtain ⟨i, rfl⟩ : ∃ i, L.get i = α := List.mem_iff_get.1 (Multiset.mem_coe.1 hα)
  have ha : 1 ≤ L.length := Fin.pos i
  induction π using Quotient.inductionOn with | _ π => ?_
  set z := L.get with hz
  let F := w.adicCompletion E
  letI : MeasurableSpace F := borel F
  haveI : BorelSpace F := ⟨rfl⟩
  have hB' : HasSatGL w (π.locRep w) (Finset.univ.val.map z) := by rw [← hBz]; exact hB
  obtain ⟨ψ, hψ, l, hl0, hW⟩ := g4 E L.length ha π w
  obtain ⟨v, g, hv, hlv⟩ := g2 E L.length π w _ hB' l hl0
  obtain ⟨Bf, hBf⟩ := g1 E L.length π hU w
  have hs := g3 E L.length π w
  obtain ⟨hq, h12'⟩ := h12 E w
  have hH : Heig (π.locRep w) v z := h12' L.length π.V (π.locRep w) v z hv
  have hq1 : (1 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w
  have hpair := h11b L.length z (h11 F L.length π.V (π.locRep w) Bf hBf v z hv.1 hH)
  have hup : ∀ j, ‖(z j : ℂ)‖ < Real.sqrt (Ideal.absNorm w.asIdeal : ℝ) := by
    intro j
    rcases Nat.lt_or_ge 1 L.length with h2 | h1
    · have := h10 F Measure.addHaar ψ hψ L.length π.V (π.locRep w) hs h2 l Bf hW hBf v z hH ⟨g, hlv⟩ j
      rwa [hq] at this
    · obtain ⟨k, hk⟩ := hpair j
      have hkj : k = j := Fin.ext (by have := k.2; have := j.2; omega)
      subst hkj
      have h0 : ‖(z k : ℂ)‖ = 1 := by
        have h00 : 0 ≤ ‖(z k : ℂ)‖ := norm_nonneg _
        nlinarith
      rw [h0, Real.lt_sqrt zero_le_one]
      simpa using hq1
  obtain ⟨k, hk⟩ := hpair i
  have hkpos : 0 < ‖(z k : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
  have hi : ‖(z i : ℂ)‖ = ‖(z k : ℂ)‖⁻¹ := eq_inv_of_mul_eq_one_right hk
  have hsq : (Ideal.absNorm w.asIdeal : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (Ideal.absNorm w.asIdeal : ℝ) :=
    (Real.sqrt_eq_rpow _).symm
  refine ⟨?_, ?_⟩
  · rw [Real.rpow_neg (by positivity), hsq, hi]
    exact inv_strictAnti₀ hkpos (hup k)
  · rw [hsq]; exact hup i

end GlobalTheory.CompanionTheory.SatakeBound

end
end
