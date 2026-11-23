module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle606
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle662
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle731
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle722
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle687
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle684
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle587
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle564
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle634
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle736
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle563
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle588
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle705
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Kernel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle308
public import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle737
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.CocycleFrob

theorem σA_frob {l : ℕ} [Fact l.Prime] (g : GQ l) (x : Ainf l) :
    Per.σA g (WittVector.frobenius x) = WittVector.frobenius (Per.σA g x) := by
  rw [WittVector.frobenius_eq_map_frobenius]
  refine WittVector.ext fun n => ?_
  rw [GlobalTheory.RingIface.sigA_coeff l g, WittVector.map_coeff, WittVector.map_coeff,
    GlobalTheory.RingIface.sigA_coeff l g, frobenius_def, frobenius_def, map_pow]

theorem cancel_left {R : Type} [CommRing R] [IsDomain R] {n : Type} [Fintype n] [DecidableEq n]
    (Y X₁ X₂ : Matrix n n R) (c : R) (hc : c ≠ 0) (hY : Y.det ≠ 0) (h : c • (Y * X₁) = c • (Y * X₂)) :
    X₁ = X₂ := by
  have h1 : Y * X₁ = Y * X₂ := by
    ext i j
    have := congrFun (congrFun h i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hc this
  have h2 := congrArg (fun Z => Y.adjugate * Z) h1
  simp only [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul] at h2
  ext i j
  have := congrFun (congrFun h2 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hY this

theorem frob_eq : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d M N : ℕ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (A A' : Matrix (Fin d) (Fin d) bk.S), A * A' = bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) bk.S) → bk.ev bk.E ^ N • Y.map WittVector.frobenius = bk.ev bk.E ^ M • (Y * A.map bk.ev) → (Y.map bk.iA).det ≠ 0 → ∀ (g : GQ l) (G Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA g) G → IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → ∀ (w : (Ainf l)ˣ), Per.σA g (bk.ev bk.E) = bk.ev bk.E * w → ∀ (P : Matrix (Fin d) (Fin d) (Ainf l)), P.map WittVector.frobenius = P → ∀ (e : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)), bk.iA (Per.σA g τ) ^ M • (Y.map bk.iA * e) = bk.iA τ ^ M • (P.map bk.iA * (Y.map (Per.σA g)).map bk.iA) → bk.iS bk.E ^ (2 * N) • e = (((↑w⁻¹ : Ainf l) ^ N) • A.map bk.ev).map bk.iA * e.map Φ * ((A'.map bk.ev).map (Per.σA g)).map bk.iA := by
  intro l _ K bk τ hτ d M N Y A A' hAA hφ hdet g G Φ _ hΦ w hw P hP e he
  obtain ⟨-, -, -, h0, h1, -⟩ := GlobalTheory.BSP.exists_discMaps l K bk
  haveI : IsDomain (bk.DA bk.ρ₀) := (GlobalTheory.BSP.discAinf_isDomain l K bk bk.ρ₀ h0 h1).1
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  have hinj : Function.Injective bk.iA := (GlobalTheory.BSP.toDisc_injective_of_topBasis l K bk (Ainf l) bk.ev ι tb bk.ρ₀ h0 h1).1
  obtain ⟨-, -, -, hστ⟩ := GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ
  have ht' : bk.iA (Per.σA g τ) ≠ 0 := by
    rw [← map_zero bk.iA]
    intro h
    have h2 := hστ g
    rw [hinj h, map_zero] at h2
    exact not_isUnit_zero h2
  have hE : bk.iA (bk.ev bk.E) ≠ 0 := by
    rw [← map_zero bk.iA]
    intro h
    exact bk.E_ne_zero (bk.ev_injective ((hinj h).trans (map_zero _).symm))
  have hu : bk.iA (w : Ainf l) ≠ 0 := fun h => by
    have := congrArg bk.iA w.mul_inv
    rw [map_mul, h, zero_mul, map_one] at this
    exact zero_ne_one this

  have hΦA : ∀ x, Φ (bk.iA x) = bk.iA (WittVector.frobenius x) := hΦ.ext
  have hσE : ∀ k : ℕ, bk.iA (Per.σA g (bk.ev bk.E ^ k)) = (bk.iA (bk.ev bk.E) * bk.iA w) ^ k := fun k => by
    rw [map_pow, hw, map_pow, map_mul]

  have hφ1 : bk.iA (bk.ev bk.E) ^ N • (Y.map WittVector.frobenius).map bk.iA =
      bk.iA (bk.ev bk.E) ^ M • (Y.map bk.iA * (A.map bk.ev).map bk.iA) := by
    have := congrArg (fun X => X.map bk.iA) hφ
    simp only [Matrix.map_smul' _ _ _ (map_mul bk.iA), Matrix.map_mul, map_pow] at this
    exact this

  have hφ2 : (bk.iA (bk.ev bk.E) * bk.iA w) ^ N • ((Y.map (Per.σA g)).map WittVector.frobenius).map bk.iA =
      (bk.iA (bk.ev bk.E) * bk.iA w) ^ M • ((Y.map (Per.σA g)).map bk.iA * ((A.map bk.ev).map (Per.σA g)).map bk.iA) := by
    have := congrArg (fun X => (X.map (Per.σA g)).map bk.iA) hφ
    simp only [Matrix.map_smul' _ _ _ (map_mul bk.iA), Matrix.map_smul' _ _ _ (map_mul (Per.σA g)),
      Matrix.map_mul] at this
    rw [hσE, hσE] at this
    have hc : ((Y.map WittVector.frobenius).map (Per.σA g)) = ((Y.map (Per.σA g)).map WittVector.frobenius) := by
      exact Matrix.ext fun i j => σA_frob g (Y i j)
    rw [hc] at this
    exact this

  have he1 : (bk.iA (bk.ev bk.E) * bk.iA w * bk.iA (Per.σA g τ)) ^ M • ((Y.map WittVector.frobenius).map bk.iA * e.map Φ) =
      (bk.iA (bk.ev bk.E) * bk.iA τ) ^ M • (P.map bk.iA * ((Y.map (Per.σA g)).map WittVector.frobenius).map bk.iA) := by
    have := congrArg (fun X => X.map Φ) he
    simp only [Matrix.map_smul' _ _ _ (map_mul Φ), Matrix.map_mul, map_pow, hΦA] at this
    have m1 : ∀ Z : Matrix (Fin d) (Fin d) (Ainf l), (Z.map bk.iA).map Φ = (Z.map WittVector.frobenius).map bk.iA :=
      fun Z => Matrix.ext fun i j => hΦA (Z i j)
    rw [m1, m1, m1, hP, ← σA_frob, hτ.1, map_mul, hw, map_mul, map_mul, map_mul] at this
    exact this
  have hA2 : ((A.map bk.ev).map (Per.σA g)).map bk.iA * ((A'.map bk.ev).map (Per.σA g)).map bk.iA =
      (bk.iA (bk.ev bk.E) * bk.iA w) ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    have := congrArg (fun X => ((X.map bk.ev).map (Per.σA g)).map bk.iA) hAA
    simp only [Matrix.map_smul' _ _ _ (map_mul bk.iA), Matrix.map_smul' _ _ _ (map_mul (Per.σA g)),
      Matrix.map_smul' _ _ _ (map_mul bk.ev), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at this
    rw [map_pow bk.ev, hσE] at this
    exact this
  have hv : bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) * bk.iA w = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hiS : bk.iS bk.E = bk.iA (bk.ev bk.E) := rfl
  rw [hiS, Matrix.map_smul' _ _ _ (map_mul bk.iA), map_pow]
  generalize (Y.map WittVector.frobenius).map bk.iA = ΦY at hφ1 he1
  generalize ((Y.map (Per.σA g)).map WittVector.frobenius).map bk.iA = ΦGY at hφ2 he1
  generalize (Y.map (Per.σA g)).map bk.iA = GY at hφ2 he
  generalize Y.map bk.iA = YY at hφ1 he hdet
  generalize (A.map bk.ev).map bk.iA = AA at hφ1 ⊢
  generalize ((A.map bk.ev).map (Per.σA g)).map bk.iA = GA at hφ2 hA2
  generalize ((A'.map bk.ev).map (Per.σA g)).map bk.iA = GA' at hA2 ⊢
  generalize P.map bk.iA = PP at he he1
  generalize e.map Φ = Φe at he1 ⊢
  generalize bk.iA (bk.ev bk.E) = E' at *
  generalize bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) = v at *
  generalize bk.iA (w : Ainf l) = u at *
  generalize bk.iA (Per.σA g τ) = t' at *
  generalize bk.iA τ = t at *
  have key : (E' ^ (2 * M) * u ^ M * t' ^ M) • (YY * (u ^ N • (AA * Φe))) =
      (E' ^ (2 * M) * u ^ M * t' ^ M) • (YY * (e * GA)) :=
    calc (E' ^ (2 * M) * u ^ M * t' ^ M) • (YY * (u ^ N • (AA * Φe)))
        = (u ^ N * (E' * u * t') ^ M) • ((E' ^ M • (YY * AA)) * Φe) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]; congr 1; ring
      _ = (u ^ N * (E' * u * t') ^ M) • ((E' ^ N • ΦY) * Φe) := by rw [hφ1]
      _ = (E' * u) ^ N • ((E' * u * t') ^ M • (ΦY * Φe)) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]; congr 1; ring
      _ = (E' * u) ^ N • ((E' * t) ^ M • (PP * ΦGY)) := by rw [he1]
      _ = (E' * t) ^ M • (PP * ((E' * u) ^ N • ΦGY)) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]; congr 1; ring
      _ = (E' * t) ^ M • (PP * ((E' * u) ^ M • (GY * GA))) := by rw [hφ2]
      _ = (E' ^ M * (E' * u) ^ M) • ((t ^ M • (PP * GY)) * GA) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]; congr 1; ring
      _ = (E' ^ M * (E' * u) ^ M) • ((t' ^ M • (YY * e)) * GA) := by rw [he]
      _ = (E' ^ (2 * M) * u ^ M * t' ^ M) • (YY * (e * GA)) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]; congr 1; ring
  have hu' : u ≠ 0 := fun h => by rw [h, mul_zero] at hv; exact zero_ne_one hv
  have hc : E' ^ (2 * M) * u ^ M * t' ^ M ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hE) (pow_ne_zero _ hu')) (pow_ne_zero _ ht')
  have hX := cancel_left YY _ _ _ hc hdet key
  calc E' ^ (2 * N) • e = (v ^ (2 * N) * (E' * u) ^ (2 * N)) • e := by
        congr 1
        rw [show v ^ (2 * N) * (E' * u) ^ (2 * N) = E' ^ (2 * N) * (v * u) ^ (2 * N) by ring, hv, one_pow, mul_one]
    _ = v ^ (2 * N) • (e * ((E' * u) ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)))) := by
        rw [Matrix.mul_smul, Matrix.mul_one, smul_smul]
    _ = v ^ (2 * N) • ((e * GA) * GA') := by rw [← hA2, Matrix.mul_assoc]
    _ = v ^ (2 * N) • ((u ^ N • (AA * Φe)) * GA') := by rw [hX]
    _ = (v ^ N • AA) * Φe * GA' := by
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
        congr 1
        rw [show v ^ (2 * N) * u ^ N = v ^ N * (v * u) ^ N by ring, hv, one_pow, mul_one]

end GlobalTheory.BSP.CocycleFrob
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem norm_pow_mul_eq_of_norm_mul_eq {R : Type*} [NormedRing R] (E : R) (q : ℝ)
    (hE : ∀ y, ‖E * y‖ = q * ‖y‖) (h : ℕ) (y : R) : ‖E ^ h * y‖ = q ^ h * ‖y‖ := by
  induction h generalizing y with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_assoc, ih, hE, pow_succ]; ring

theorem exists_discStep : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ (φ : A →+* A), φ (s X) = s X ^ l → ∀ (Φ : Disc l (s X) bk.ρ₀ →+* Disc l (s X) bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) φ Φ → ∀ (κ : Type) (c : κ → κ → A), (∀ i (n : ℕ), {j | c i j ∉ (bk.J ^ n).map s}.Finite) → ∀ (h : ℕ) (V : κ → Disc l (s X) bk.ρ₀), (∀ j, HasSum (fun i => Φ (V i) * toDisc l (s X) bk.ρ₀ (c i j)) (toDisc l (s X) bk.ρ₀ (s bk.E) ^ h * V j)) → ∀ (ρ ρ' : ℝ≥0), bk.ρ₀ ≤ ρ → ρ < 1 → ρ' ^ l = ρ → ∀ (R : Disc l (s X) ρ →+* Disc l (s X) bk.ρ₀) (R' : Disc l (s X) ρ' →+* Disc l (s X) bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id A) R → IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id A) R' → ∀ (U : κ → Disc l (s X) ρ) (C : ℝ), 0 ≤ C → Filter.Tendsto U Filter.cofinite (nhds 0) → (∀ j, R (U j) = V j) → (∀ j, ‖U j‖ ≤ C) → ∃ U' : κ → Disc l (s X) ρ', Filter.Tendsto U' Filter.cofinite (nhds 0) ∧ (∀ j, R' (U' j) = V j) ∧ ∀ j, (ρ' : ℝ) ^ (bk.Ep.natDegree * h) * ‖U' j‖ ≤ C := by
  intro l _ K bk A _ s ι tb φ hφ Φ hΦ κ c hc h V hV ρ ρ' hρ₀ hρ1 hρ' R R' hR hR' U C hC hU hRU hUC
  obtain ⟨-, -, ⟨hρ₀pos, hρ₀1, -⟩, -⟩ := GlobalTheory.T.breuilKisin_flat_radius_ideal_facts l K bk
  have hl1 : 1 ≤ l := (Fact.out : l.Prime).one_lt.le
  have hρpos : 0 < ρ := hρ₀pos.trans_le hρ₀
  have hρ'pos : 0 < ρ' := by
    rcases (show (0 : ℝ≥0) ≤ ρ' from zero_le).eq_or_lt with h0 | h0
    · rw [← h0, zero_pow (by omega)] at hρ'
      exact absurd hρ' hρpos.ne
    · exact h0
  have hρ'1 : ρ' < 1 := by
    by_contra hh
    push_neg at hh
    have h2 := one_le_pow₀ hh (n := l)
    rw [hρ'] at h2
    exact absurd hρ1 (not_lt.2 h2)
  have hρρ' : ρ ≤ ρ' := by rw [← hρ']; exact pow_le_of_le_one zero_le hρ'1.le (by omega)

  obtain ⟨Φ', hΦ'⟩ := GlobalTheory.T.exists_closedDiscExtension_of_pow_dvd l A A φ (s X) (s X) ρ ρ' l hρ'pos (by rw [hφ]) hρ'.le
  have hc1 := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A (s X) ρ).2.2.2 A A (s X) (s X) ρ' bk.ρ₀ φ (RingHom.id A) Φ' R' hΦ' hR'
  have hc2 := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A (s X) ρ).2.2.2 A A (s X) (s X) bk.ρ₀ bk.ρ₀ (RingHom.id A) φ R Φ hR hΦ
  rw [RingHom.id_comp] at hc1
  rw [RingHom.comp_id] at hc2
  have hcomm : ∀ x, R' (Φ' x) = Φ (R x) := fun x => RingHom.congr_fun (hc1.unique hc2) x
  haveI : IsUltrametricDist (Disc l (s X) ρ') := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A (s X) ρ').1
  haveI : NonarchimedeanAddGroup (Disc l (s X) ρ') := IsUltrametricDist.nonarchimedeanAddGroup

  have hUn : Filter.Tendsto (fun i => ‖U i‖) Filter.cofinite (nhds 0) := tendsto_zero_iff_norm_tendsto_zero.1 hU
  have hTle : ∀ i j, ‖Φ' (U i) * toDisc l (s X) ρ' (c i j)‖ ≤ ‖U i‖ * ‖toDisc l (s X) ρ' (c i j)‖ := fun i j =>
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hΦ'.norm_le _) (norm_nonneg _))
  have hTle' : ∀ i j, ‖Φ' (U i) * toDisc l (s X) ρ' (c i j)‖ ≤ ‖U i‖ := fun i j =>
    (hTle i j).trans (mul_le_of_le_one_right (norm_nonneg _) (norm_toDisc_le _))
  have hsum : ∀ j, Summable fun i => Φ' (U i) * toDisc l (s X) ρ' (c i j) := fun j =>
    NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (squeeze_zero_norm (fun i => hTle' i j) hUn)
  set Z : κ → Disc l (s X) ρ' := fun j => ∑' i, Φ' (U i) * toDisc l (s X) ρ' (c i j) with hZdef
  have hZC : ∀ j, ‖Z j‖ ≤ C := fun j =>
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hC fun i => (hTle' i j).trans (hUC i)
  have hR'c : Continuous R' :=
    AddMonoidHomClass.continuous_of_bound R' 1 fun y => (hR'.norm_le y).trans (one_mul _).ge
  have hRZ : ∀ j, R' (Z j) = toDisc l (s X) bk.ρ₀ (s bk.E) ^ h * V j := fun j => by
    have h1 := (hsum j).hasSum.map R' hR'c
    have h2 : (R' ∘ fun i => Φ' (U i) * toDisc l (s X) ρ' (c i j)) =
        fun i => Φ (V i) * toDisc l (s X) bk.ρ₀ (c i j) := by
      funext i
      simp only [Function.comp_apply, map_mul, hcomm, hRU, hR'.ext, RingHom.id_apply]
    rw [h2] at h1
    exact h1.unique (hV j)

  have hsmall : ∀ r : ℝ, 0 < r → {j | r < ‖Z j‖}.Finite := by
    intro r hr
    have hF : {i | r < ‖U i‖}.Finite := by
      have := Filter.eventually_cofinite.1 (hUn.eventually (ge_mem_nhds hr))
      simpa only [not_le] using this
    obtain ⟨n, hn⟩ := GlobalTheory.T.norm_baseRingToClosedDisc_J_pow_small l K bk A s ρ' hρ'pos hρ'1 (r / (C + 1)) (by positivity)
    refine (hF.biUnion fun i _ => hc i n).subset ?_
    intro j hj
    by_contra hj'
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_not] at hj'
    refine (not_le.2 (show r < ‖Z j‖ from hj)) ?_
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hr.le fun i => ?_
    by_cases hi : r < ‖U i‖
    · refine (hTle i j).trans ((mul_le_mul (hUC i) (hn _ (hj' i hi)) (norm_nonneg _) hC).trans ?_)
      rw [mul_div_assoc', div_le_iff₀ (by linarith)]
      nlinarith
    · exact (hTle' i j).trans (not_lt.1 hi)
  have hZ : Filter.Tendsto Z Filter.cofinite (nhds 0) := by
    refine Metric.tendsto_nhds.2 fun ε hε => Filter.eventually_cofinite.2 ((hsmall (ε / 2) (by linarith)).subset ?_)
    intro j hj
    simp only [Set.mem_setOf_eq, dist_zero_right, not_lt] at hj ⊢
    linarith

  obtain ⟨hnorm', hdiv'⟩ := GlobalTheory.T.eisenstein_div_closedDisc_of_topBasis l K bk A s ι tb ρ' (hρ₀.trans hρρ') hρ'1
  obtain ⟨hnorm₀, -⟩ := GlobalTheory.T.eisenstein_div_closedDisc_of_topBasis l K bk A s ι tb bk.ρ₀ le_rfl hρ₀1
  choose U' hU' using fun j => hdiv' R' hR' h (Z j) ⟨V j, hRZ j⟩
  have hq : (0 : ℝ) < (ρ' : ℝ) ^ (bk.Ep.natDegree * h) := by positivity
  have hnZ : ∀ j, ‖Z j‖ = (ρ' : ℝ) ^ (bk.Ep.natDegree * h) * ‖U' j‖ := fun j => by
    rw [hU' j, norm_pow_mul_eq_of_norm_mul_eq _ _ hnorm' h, pow_mul]
  refine ⟨U', ?_, ?_, fun j => (hnZ j).symm.trans_le (hZC j)⟩
  · have he : ∀ j, ‖U' j‖ = ((ρ' : ℝ) ^ (bk.Ep.natDegree * h))⁻¹ * ‖Z j‖ := fun j => by
      rw [hnZ j, inv_mul_cancel_left₀ hq.ne']
    refine squeeze_zero_norm (fun j => (he j).le) ?_
    simpa using (tendsto_zero_iff_norm_tendsto_zero.1 hZ).const_mul ((ρ' : ℝ) ^ (bk.Ep.natDegree * h))⁻¹
  · intro j
    have h1 : toDisc l (s X) bk.ρ₀ (s bk.E) ^ h * (R' (U' j) - V j) = 0 := by
      have h2 := hRZ j
      rw [hU' j, map_mul, map_pow, hR'.ext, RingHom.id_apply] at h2
      rw [mul_sub, h2, sub_self]
    have h3 := congrArg norm h1
    rw [norm_pow_mul_eq_of_norm_mul_eq _ _ hnorm₀ h, norm_zero] at h3
    have h4 : (0 : ℝ) < ((bk.ρ₀ : ℝ) ^ bk.Ep.natDegree) ^ h := by positivity
    exact sub_eq_zero.1 (norm_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left h4.ne'))

end GlobalTheory.BSP
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem GlobalTheory.BKLim.descend_rightInverse : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (M : ℕ), ∃ r : ℕ, ∀ (d d' n : ℕ) (R : Matrix (Fin d) (Fin d') (bk.S)) (a : Matrix (Fin d') (Fin d) (Ainf l)), (∀ i j, (l : Ainf l) ^ n ∣ (R.map bk.ev * a - τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l))) i j) → ∃ G : Matrix (Fin d') (Fin d) (bk.S), (∀ i j, (l : bk.S) ^ n ∣ (R * G - (l : bk.S) ^ r • (1 : Matrix (Fin d) (Fin d) (bk.S))) i j) := by
  intro l _ K bk τ hτ M
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  obtain ⟨r, hr⟩ := GlobalTheory.BSP.pow_l_mem_span_coeff l K bk τ hτ ι TB M
  obtain ⟨t, ht⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hr
  refine ⟨r, fun d d' n R a h => ?_⟩
  refine ⟨∑ k ∈ t.support, t k • (a.map (TB.c k)), fun i j => ?_⟩
  have hl : ∀ k (y : Ainf l), TB.c k ((l : Ainf l) ^ n * y) = (l : bk.S) ^ n * TB.c k y := by
    intro k y
    have e : (l : Ainf l) ^ n = bk.ev ((l : bk.S) ^ n) := by rw [map_pow, map_natCast]
    rw [e, TB.c_mul]
  obtain ⟨y, hy⟩ := h i j
  rw [Matrix.sub_apply] at hy
  have hy' := sub_eq_iff_eq_add.1 hy
  have hG : (R * ∑ k ∈ t.support, t k • (a.map (TB.c k))) i j = ∑ k ∈ t.support, t k * TB.c k ((R.map bk.ev * a) i j) := by

    simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    Finset.mul_sum, map_sum, TB.c_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [Matrix.sub_apply, hG, hy']
  simp only [map_add (f := _), hl, mul_add, Finset.sum_add_distrib]
  refine ⟨∑ k ∈ t.support, t k * TB.c k y, ?_⟩
  rw [← ht]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Finsupp.sum, Finset.mul_sum]
    rw [add_sub_cancel_right]
    exact Finset.sum_congr rfl fun _ _ => by ring
  · simp only [Matrix.smul_apply, Matrix.one_apply_ne hij, smul_zero, map_zero, mul_zero, Finset.sum_const_zero,
      add_zero, sub_zero, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP

private theorem map_mulVec_fun {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (f : R →+* S)
    (M : Matrix (Fin d) (Fin d) R) (v : Fin d → R) :
    (fun a => f ((M *ᵥ v) a)) = M.map f *ᵥ fun a => f (v a) := funext fun a => RingHom.map_mulVec f M v a

private theorem det_map_ringHom {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (f : R →+* S)
    (M : Matrix (Fin d) (Fin d) R) : (M.map f).det = f M.det := (RingHom.map_det f M).symm

private theorem adjugate_map_ringHom {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (f : R →+* S)
    (M : Matrix (Fin d) (Fin d) R) : (M.map f).adjugate = M.adjugate.map f := (RingHom.map_adjugate f M).symm

theorem rational_in_columns : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ) (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (Z1 : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), (Y1.map (inclW l)).det ≠ 0 → (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W * Z1.map j = Y1.map bk.iA) → ∀ y, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) y → ∃ (δ : bk.S) (c : Fin d → bk.S), δ ≠ 0 ∧ (fun a => bk.ev δ * y a) = Y1 *ᵥ fun a => bk.ev (c a) := by
  intro l _ K bk τ hτ d ρ hρ s Y1 Z1 hdet hWZ y hy
  obtain ⟨x, hx⟩ := hy
  have hl : (1 : ℝ≥0) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have he : (0 : ℝ) < bk.Ep.natDegree := by exact_mod_cast bk.deg_pos
  have hρ0 : 0 < bk.ρ₀ := NNReal.rpow_pos (zero_lt_one.trans hl)
  have hρ1 : bk.ρ₀ < 1 := NNReal.rpow_lt_one_of_one_lt_of_neg hl (by simp only [Left.neg_neg_iff]; positivity)
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hinj : Function.Injective bk.iA := (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk (Ainf l) bk.ev ι TB bk.ρ₀ hρ0 hρ1).1
  have hXn : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀ := by
    simpa using norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) 1 hρ0
  let j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map (l := l) (u := (X : bk.S)) (ρ := bk.ρ₀) bk.ev hXn
  have hj : IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j := isDiscMap_map _ _
  have hWZj := hWZ j hj
  have hxj := hx j hj
  have hD : Y1.det ≠ 0 := by
    intro h; apply hdet; rw [det_map_ringHom, h, map_zero]
  have hdetA : bk.iA Y1.det = (s.W).det * j Z1.det := by
    rw [← det_map_ringHom, ← hWZj, det_mul, det_map_ringHom]
  have hΔ : Z1.det ≠ 0 := by
    intro h; apply hD; apply hinj; rw [hdetA, h, map_zero, mul_zero, map_zero]
  have h1 : Y1.map bk.iA *ᵥ (fun a => j ((Z1.adjugate *ᵥ x) a)) = j Z1.det • fun a => bk.iA (y a) := by
    rw [map_mulVec_fun j, ← hWZj, ← adjugate_map_ringHom, mulVec_mulVec, Matrix.mul_assoc, mul_adjugate,
      det_map_ringHom, Matrix.mul_smul, Matrix.mul_one, smul_mulVec, hxj]
  have h2 : bk.iA Y1.det • (fun a => j ((Z1.adjugate *ᵥ x) a)) =
      j Z1.det • fun a => bk.iA ((Y1.adjugate *ᵥ y) a) := by
    have h3 : (Y1.map bk.iA).adjugate *ᵥ (Y1.map bk.iA *ᵥ (fun a => j ((Z1.adjugate *ᵥ x) a))) =
        (Y1.map bk.iA).adjugate *ᵥ (j Z1.det • fun a => bk.iA (y a)) := by rw [h1]
    rw [mulVec_mulVec, adjugate_mul, det_map_ringHom, smul_mulVec, one_mulVec, mulVec_smul,
      adjugate_map_ringHom, ← map_mulVec_fun] at h3
    exact h3
  have key : ∀ a, ∃ δ c : bk.S, δ ≠ 0 ∧ bk.ev δ * (Y1.adjugate *ᵥ y) a = bk.ev c * Y1.det := fun a =>
    GlobalTheory.T.ainf_closedDisc_linearDisjoint_over_powerSeries l K bk (Ainf l) bk.ev ι TB j hj ((Y1.adjugate *ᵥ y) a) Y1.det ((Z1.adjugate *ᵥ x) a) Z1.det
      hΔ hD (by
        have h4 := congrFun h2 a
        simp only [Pi.smul_apply, smul_eq_mul] at h4
        calc _ = j Z1.det * bk.iA ((Y1.adjugate *ᵥ y) a) := mul_comm _ _
          _ = _ := h4.symm)
  choose δs cs hδ hc using key
  refine ⟨∏ a, δs a, fun a => cs a * ∏ b ∈ Finset.univ.erase a, δs b,
    Finset.prod_ne_zero_iff.2 fun a _ => hδ a, ?_⟩
  have hw : ∀ a, bk.ev (∏ b, δs b) * (Y1.adjugate *ᵥ y) a =
      Y1.det * bk.ev (cs a * ∏ b ∈ Finset.univ.erase a, δs b) := by
    intro a
    rw [← Finset.mul_prod_erase Finset.univ δs (Finset.mem_univ a), map_mul, map_mul, mul_comm (bk.ev (δs a)),
      mul_assoc, hc a]
    ring
  have hYw : Y1 *ᵥ (Y1.adjugate *ᵥ y) = Y1.det • y := by
    rw [mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec]
  have hcancel : Y1.det • (fun a => bk.ev (∏ b, δs b) * y a) =
      Y1.det • (Y1 *ᵥ fun a => bk.ev (cs a * ∏ b ∈ Finset.univ.erase a, δs b)) := by
    calc Y1.det • (fun a => bk.ev (∏ b, δs b) * y a) = bk.ev (∏ b, δs b) • (Y1 *ᵥ (Y1.adjugate *ᵥ y)) := by
          rw [hYw]; funext a; simp only [Pi.smul_apply, smul_eq_mul]; ring
      _ = Y1 *ᵥ (bk.ev (∏ b, δs b) • (Y1.adjugate *ᵥ y)) := by rw [mulVec_smul]
      _ = Y1 *ᵥ (Y1.det • fun a => bk.ev (cs a * ∏ b ∈ Finset.univ.erase a, δs b)) := by
          congr 1; funext a; simp only [Pi.smul_apply, smul_eq_mul]; exact hw a
      _ = _ := by rw [mulVec_smul]
  exact smul_right_injective _ hD hcancel

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.ladic_descent_step_to_OE : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (κ : Type) [Fintype κ] (x b : κ → WCb l) (c : κ → κ → WCb l), (∀ i j, c i j ∈ bk.OE) → (∀ j, b j ∈ bk.OE) → (∀ j, x j = ∑ i, frobW l (x i) * c i j + b j) → (∀ g : ↥(GK K), bk.FixFlat g → ∀ j, galW l (g : GQ l) (x j) = x j) → ∃ v x' b' : κ → WCb l, (∀ j, v j ∈ bk.OE) ∧ (∀ j, b' j ∈ bk.OE) ∧ (∀ j, x j = v j + ((l : ℕ) : WCb l) * x' j) ∧ (∀ j, x' j = ∑ i, frobW l (x' i) * c i j + b' j) ∧ ∀ g : ↥(GK K), bk.FixFlat g → ∀ j, galW l (g : GQ l) (x' j) = x' j := by
  first | exact @GlobalTheory.BSP.BK.descent_step | exact GlobalTheory.BSP.BK.descent_step | (intros; apply GlobalTheory.BSP.BK.descent_step <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.prime_dvd_ainfEnvelope_of_galois_sections : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X)) (κ : Type) [Fintype κ] (x : κ → En.Q.A) (c : κ → κ → En.Q.A) (h : ℕ), (∀ j, En.inl.f (bk.ev bk.E) ^ h * x j = ∑ i, En.Q.D.φ (x i) * c i j) → (∀ (g : ↥(GK K)) (s : Hom En.Q (ainfObj K)), s.comp En.inl = Hom.id _ → s.comp En.inr = (ainfHom K g).comp bk.ι → ∀ j, ((l : ℕ) : (ainfObj K).A) ∣ s.f (x j)) → ∀ j, ((l : ℕ) : En.Q.A) ∣ x j := by
  first | exact @GlobalTheory.BSP.l_dvd_of_galois_sections | exact GlobalTheory.BSP.l_dvd_of_galois_sections | (intros; apply GlobalTheory.BSP.l_dvd_of_galois_sections <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

theorem _root_.GlobalTheory.T.exists_pow_mem_span_coeff_period_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (ι : Type) (TB : TopBasis bk.ev bk.J ι) (M : ℕ), ∃ r : ℕ, (l : bk.S) ^ r ∈ Ideal.span (Set.range fun i => TB.c i (τ ^ M)) := by
  first | exact @GlobalTheory.BSP.pow_l_mem_span_coeff | exact GlobalTheory.BSP.pow_l_mem_span_coeff | (intros; apply GlobalTheory.BSP.pow_l_mem_span_coeff <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module

theorem _root_.GlobalTheory.T.exists_exactLocalConditionData_at_place : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i), tableLineDegreeTwo.adm20 D HW F → AdmissibleParameterJ.ConclusionJa D → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.admG2 i r ρ π →
    TruncatedSeriesCountingIdentities.admG3 i r ρ π → TruncatedSeriesCountingIdentities.FamilyContinuous i r → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i → 5 ≤ D.nd.l i →
    D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d →
    (∀ (n : ℕ) [NeZero n] (up : ZMod n → Bool) (τ : ZMod n → D.what₂.Tau), ∃ (h w η : ZMod n → ℕ) (typ : ZMod n → Bool)
      (U : ZMod n → Multiset ℤ), tableLineDegreeTwo.PositionHyps (D.nd.l i) n D.R.t h w η typ U ∧ ∀ (a : ZMod n) (b : ℤ),
        ((U a).count (b + w a) = 1 ↔ (b : ℚ) ∈ AdmissibleParameterJ.JW D (up a) (D.nd.j i) (τ a)) ∧ (U a).count (b + w a) ≤ 1) →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      ∃ (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)) (_ : Irreducible lam)
        (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
        (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
        (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
        (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
        SetC HW r ρ π C hA lam θ h w' η typ U := by
  first | exact @GlobalTheory.UseLocInst.exists_setC | exact GlobalTheory.UseLocInst.exists_setC | (intros; apply GlobalTheory.UseLocInst.exists_setC <;> assumption)
end
