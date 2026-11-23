module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle579
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle580
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle126
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle581
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle582
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.isPrismCover_of_stable_maximal_map_ne_top : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C : Obj l R) (h : Hom B C), Stable h → (∀ 𝔪 : Ideal B.A, 𝔪.IsMaximal → 𝔪.map h.f ≠ ⊤) → Cover h := by
  first | exact @GlobalTheory.BSP.cover_of_stable_of_map_ne_top | exact GlobalTheory.BSP.cover_of_stable_of_map_ne_top | (intros; apply GlobalTheory.BSP.cover_of_stable_of_map_ne_top <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_kernel_lattice_equivariant_modPow : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (d d' n : ℕ) (ρ : Γ →* GL (Fin d) ℤ_[l]) (ρ' : Γ →* GL (Fin d') ℤ_[l]) (Pi : Matrix (Fin d) (Fin d') (ℤ_[l])), Onto (fun g => (ρ g).val) (fun g => (ρ' g).val) Pi n → ∃ (f : Matrix (Fin d') (Fin d') (ℤ_[l])) (ρ'' : Γ →* GL (Fin d') ℤ_[l]), f.det ≠ 0 ∧ (∀ g, f * (ρ'' g).val = (ρ' g).val * f) ∧ ∀ v : Fin d' → ℤ_[l], (∀ i, (l : ℤ_[l]) ^ n ∣ (Pi *ᵥ v) i) ↔ ∃ w, v = f *ᵥ w := by
  first | exact @GlobalTheory.KerLat.exists_kernel_lattice | exact GlobalTheory.KerLat.exists_kernel_lattice | (intros; apply GlobalTheory.KerLat.exists_kernel_lattice; all_goals assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.frame_ainf_matrix_frobenius_galois_eqs : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (Y Y' : Matrix (Fin d) (Fin d) (Ainf l)), Y.map (inclW l) = inclW l τ ^ N • F.T → Y * Y' = τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → Y.map WittVector.frobenius = Y * F.A.map bk.ev ∧ (∀ g : ↥(GK K), τ ^ N • ((ρ g).map (Per.zA l) * Y.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ N • (Y * F.ε g)) ∧ ∀ g : ↥(GK K), bk.ev bk.E ^ N • (F.ε g * F.A.map (fun s => Per.σA (g : GQ l) (bk.ev s))) = Per.σA (g : GQ l) (bk.ev bk.E) ^ N • (F.A.map bk.ev * (F.ε g).map WittVector.frobenius) := by
  first | (exact @GlobalTheory.FrameEq.frame_Y_eqs) | (exact GlobalTheory.FrameEq.frame_Y_eqs) | (intros; apply GlobalTheory.FrameEq.frame_Y_eqs  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.GalAdapted

theorem gal_V : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (H : Hodge C (bk.ev bk.E) (fun g => (ρ g).map (zOm l)) K) (g : ↥(GK K)) (w : Ainf l), Per.σA (g : GQ l) (bk.ev bk.E) = bk.ev bk.E * w → (ρ g).map ((aDp l).comp (Per.zA l)) * H.V.map (Per.σDp (g : GQ l)) * Matrix.diagonal (fun j => aDp l w ^ H.p j) = aDp l w ^ H.q • H.V := by
  intro l _ K bk C d ρ H g w hw
  have hinj : Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) := (BdRField.bdR_isField l).2.1
  obtain ⟨u, hu, -⟩ := AdaptedHodge.xi_unit_fil C (bk.ev bk.E) bk.span_ev
  have hΞ : IsUnit (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E))) := hu ▸ u.isUnit
  have hξ : Per.σD (g : GQ l) (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E))) =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l w) := by
    rw [ActLaws.σD_alg, ActLaws.σDp_aDp, hw, map_mul, map_mul]
  have hmap : ∀ z : ℤ_[l], C.o (zOm l z) = aDp l (Per.zA l z) := fun z => C.o_sec.z z
  have hinv := H.inv g g.2
  ext i j
  apply hinj
  refine (hΞ.pow (H.p j)).mul_left_cancel ?_
  have hσ : ∀ k, (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l w)) ^ H.q *
      Per.σD (g : GQ l) (H.Q k j) = (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l w)) ^ H.p j *
      algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp (g : GQ l) (H.V k j)) := by
    intro k
    have := congrArg (Per.σD (g : GQ l)) (H.Q_eq k j)
    rw [map_mul, map_pow, hξ, ActLaws.σD_alg, map_mul, map_pow, ActLaws.σDp_aDp, hw, map_mul, map_mul, map_pow, map_mul] at this
    rw [this]
  have hI : ∑ k, algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l (ρ g i k))) * Per.σD (g : GQ l) (H.Q k j) = H.Q i j := by
    have := congrFun (congrFun hinv i) j
    simpa [Matrix.mul_apply, hmap] using this
  rw [Matrix.mul_diagonal, Matrix.smul_apply]

  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, RingHom.comp_apply,
  map_mul, map_sum, map_pow]
  have e1 : algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) ^ H.p j *
      (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l w) ^ H.q * algebraMap (Per.BdRp l) (Per.BdR l) (H.V i j)) =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l w) ^ H.q *
        (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) ^ H.q * H.Q i j) := by
    rw [H.Q_eq i j, map_mul, map_pow]; ring
  rw [e1, ← hI]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  linear_combination -(algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l (ρ g i k)))) * hσ k

end GlobalTheory.BKLim.GalAdapted
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.basis_matrix_map_cancel_left : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s) (C : Type) [CommRing C] (F : bk.DS bk.ρ₀ →+* C), F (toDisc l (X : bk.S) bk.ρ₀ bk.E) ∈ nonZeroDivisors C → ∀ M M' : Matrix (Fin d) (Fin d) C, ht.bas.map F * M = ht.bas.map F * M' → M = M' := by
  first | exact @GlobalTheory.BSP.Height.bas_map_cancel_left | exact GlobalTheory.BSP.Height.bas_map_cancel_left | (intros; apply GlobalTheory.BSP.Height.bas_map_cancel_left <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_trivial_cocycle_crystalline_period_data : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (s : Seed bk d ρ τ), ∃ s' : WSeed bk d ρ τ, ∀ g, s'.κ g = 1 := by
  first | exact @GlobalTheory.BKLim.wseed_of_seed | exact GlobalTheory.BKLim.wseed_of_seed | (intros; apply GlobalTheory.BKLim.wseed_of_seed <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.frobenius_galois_relation_frame_ainf : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), Y.map (inclW l) = inclW l τ ^ N • F.T → ∀ g : ↥(GK K), (bk.ev bk.E * τ) ^ N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * (Y.map WittVector.frobenius).map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) (bk.ev bk.E * τ) ^ N • (Y.map WittVector.frobenius * (F.ε g).map WittVector.frobenius) := by
  first | exact @GlobalTheory.GalPhi.galPhi | exact GlobalTheory.GalPhi.galPhi | (intros; apply GlobalTheory.GalPhi.galPhi <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.galois_tauPow_frame_ainf : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), Y.map (inclW l) = inclW l τ ^ N • F.T → ∀ g : ↥(GK K), τ ^ N • ((ρ g).map (Per.zA l) * Y.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ N • (Y * F.ε g) := by
  first | (exact @GlobalTheory.BKLim.gal_tauPow_frame) | (exact GlobalTheory.BKLim.gal_tauPow_frame) | (intros; apply GlobalTheory.BKLim.gal_tauPow_frame  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.prism_cover_injective_and_descent : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C : Obj l R) (h : Hom B C), Cover h → Function.Injective h.f ∧ ∀ (D : Obj l R) (p q : Hom C D), IsPO h h p q → ∀ c, p.f c = q.f c → c ∈ h.f.range := by
  first | exact @GlobalTheory.BSP.cover_injective_and_descent | exact GlobalTheory.BSP.cover_injective_and_descent | (intros; apply GlobalTheory.BSP.cover_injective_and_descent <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.semilinear_projective_module_compose : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C : Obj l R) (h : Hom B C), Cover h → ∀ (A : Type) [CommRing A] (k : A →+* B.A) (N : Type) [AddCommGroup N] [Module A N] [Module.Finite A N] [Module.Projective A N] (N' : Type) [AddCommGroup N'] [Module B.A N'] [Module.Finite B.A N'] [Module.Projective B.A N'] (N'' : Type) [AddCommGroup N''] [Module C.A N''] (u : N →ₛₗ[k] N') (v : N' →ₛₗ[h.f] N'') (w : N →ₛₗ[h.f.comp k] N''), (∀ x, w x = v (u x)) → SemiBC v → SemiBC w → SemiBC u := by
  first | exact @GlobalTheory.BSP.semiBC_of_cover | exact GlobalTheory.BSP.semiBC_of_cover | (intros; apply GlobalTheory.BSP.semiBC_of_cover <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisinLatticeFrame_cocycles_linked : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N N' d d' n : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') (ℤ_[l])) (F : Frame bk N d ρ) (F' : Frame bk N' d' ρ') (Pi : Matrix (Fin d) (Fin d') (ℤ_[l])) (R : Matrix (Fin d) (Fin d') (bk.S)), (∀ g i j, (l : ℤ_[l]) ^ n ∣ (Pi * ρ' g - ρ g * Pi) i j) → (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * F'.T - F.T * R.map bk.evW) i j) → ∀ (g : ↥(GK K)) i j, (l : Ainf l) ^ n ∣ (F.ε g * (R.map bk.ev).map (Per.σA (g : GQ l)) - R.map bk.ev * F'.ε g) i j := by
  first | exact @GlobalTheory.BKLim.LinkCocycle.main | exact GlobalTheory.BKLim.LinkCocycle.main | (intros; apply GlobalTheory.BKLim.LinkCocycle.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.deRham_filtration_bounds_invariant_coordinates : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (N : ℕ), DdR (P.PD K) (qRep ρ) ≤ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) (-(N : ℤ)) → DdR (P.PD K) (qRep ρ) ⊓ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) ((N : ℤ) + 1) = ⊥ → ∀ c : Fin d → P.R.BdR, (∀ g : ↥(GK K), (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) *ᵥ (fun i => P.actQdR (g : GQ l) (c i)) = c) → c ≠ 0 → (∀ i, c i ∈ (P.PD K).Fil (-(N : ℤ))) ∧ ¬ ∀ i, c i ∈ (P.PD K).Fil ((N : ℤ) + 1) := by
  first | exact @GlobalTheory.DRMat.invariant_coord_bounds | exact GlobalTheory.DRMat.invariant_coord_bounds | (intros; apply GlobalTheory.DRMat.invariant_coord_bounds <;> assumption)
end
