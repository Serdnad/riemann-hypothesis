module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle476
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle293
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle017
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle026
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle477
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle239
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle474
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle202
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle021
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle023
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle027
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle478
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.LineUnit

open GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open scoped NNReal

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} {k : ℕ}

theorem exists_lt_nnnorm (v : HeightOneSpectrum (𝓞 F)) (C : ℝ≥0) : ∃ t : Fv F v, C < ‖t‖₊ := by
  letI : NontriviallyNormedField (Fv F v) := Valued.toNontriviallyNormedField (Fv F v) (WithZero (Multiplicative ℤ))
  obtain ⟨t, ht⟩ := NormedField.exists_lt_norm (Fv F v) (C : ℝ)
  exact ⟨t, by exact_mod_cast ht⟩

theorem valBar_smul (τ : E →ₐ[F] FvBar F v) (t : Fv F v) (y : Fv F v ⊗[F] E) :
    valBar F v (finEmb F v τ (t • y)) = ‖t‖₊ * valBar F v (finEmb F v τ y) := by
  rw [map_smul, Algebra.smul_def, map_mul]
  congr 1
  exact absBar_algebraMap F v t

theorem mem_intLoc_iff_valBar {y : Fv F v ⊗[F] E} :
    y ∈ intLoc F E v ↔ ∀ τ : E →ₐ[F] FvBar F v, valBar F v (finEmb F v τ y) ≤ 1 :=
  mem_intLoc_iff_absFin_le_one.trans (absFin_le_iff F v)

theorem exists_valBar_ne_zero {u l : Fin k → Fv F v ⊗[F] E} (h : ∑ j, l j * u j = 1) (τ : E →ₐ[F] FvBar F v) :
    ∃ j, valBar F v (finEmb F v τ (u j)) ≠ 0 := by
  by_contra hc
  push Not at hc
  have := congrArg (finEmb F v τ) h

  rw [map_sum, map_one, Finset.sum_eq_zero fun j _ => by
  rw [map_mul, (Valuation.zero_iff _).1 (hc j), mul_zero]] at this
  exact zero_ne_one this

theorem mem_intLoc_of_stable {u l : Fin k → Fv F v ⊗[F] E} (h : ∑ j, l j * u j = 1) {c : Fv F v ⊗[F] E}
    (hc : ∀ a, (∀ j, a * u j ∈ intLoc F E v) → ∀ j, c * a * u j ∈ intLoc F E v) : c ∈ intLoc F E v := by
  obtain ⟨t, ht⟩ := exists_lt_nnnorm v (Finset.univ.sup fun j => absFin F v (u j))
  have ht0 : ‖t‖₊ ≠ 0 := (lt_of_le_of_lt zero_le ht).ne'
  have h0 : ∀ j, (t⁻¹ • (1 : Fv F v ⊗[F] E)) * u j ∈ intLoc F E v := fun j => by
    rw [smul_mul_assoc, one_mul, mem_intLoc_iff_valBar]
    intro τ
    rw [valBar_smul, nnnorm_inv, inv_mul_le_iff₀ (pos_iff_ne_zero.2 ht0), mul_one]
    exact (le_absFin F v τ (u j)).trans
      ((Finset.le_sup (f := fun j => absFin F v (u j)) (Finset.mem_univ j)).trans ht.le)
  have hk : ∀ m : ℕ, ∀ j, c ^ m * (t⁻¹ • (1 : Fv F v ⊗[F] E)) * u j ∈ intLoc F E v := fun m => by
    induction m with
    | zero => simpa only [pow_zero, one_mul] using h0
    | succ m ih =>
      intro j
      have := hc _ ih j
      rwa [← mul_assoc, ← pow_succ'] at this
  rw [mem_intLoc_iff_valBar]
  intro τ
  obtain ⟨j, hj⟩ := exists_valBar_ne_zero h τ
  by_contra hlt
  rw [not_le] at hlt
  have hpos : 0 < ‖t‖₊⁻¹ * valBar F v (finEmb F v τ (u j)) :=
    mul_pos (inv_pos.2 (pos_iff_ne_zero.2 ht0)) (pos_iff_ne_zero.2 hj)
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (‖t‖₊⁻¹ * valBar F v (finEmb F v τ (u j)))⁻¹ hlt
  have h1 := mem_intLoc_iff_valBar.1 (hk m j) τ
  rw [mul_assoc, smul_mul_assoc, one_mul, map_mul, map_mul, map_pow, map_pow, valBar_smul, nnnorm_inv,
    ← le_mul_inv_iff₀ hpos, one_mul] at h1
  exact absurd h1 (not_le.2 hm)

theorem isUnit_of_reflect {u l : Fin k → Fv F v ⊗[F] E} (h : ∑ j, l j * u j = 1) {c : Fv F v ⊗[F] E}
    (hc : ∀ a, (∀ j, c * a * u j ∈ intLoc F E v) → ∀ j, a * u j ∈ intLoc F E v) : IsUnit c := by
  haveI : IsArtinianRing (Fv F v ⊗[F] E) := IsArtinianRing.of_finite (Fv F v) _
  refine IsArtinianRing.isUnit_of_mem_nonZeroDivisors (mem_nonZeroDivisors_iff_left.2 fun a ha => ?_)
  refine absFin_eq_zero_iff.1 (le_antisymm ((absFin_le_iff F v).2 fun τ => ?_) zero_le)
  by_contra hne
  have hpa : 0 < valBar F v (finEmb F v τ a) := not_le.1 hne
  obtain ⟨j, hj⟩ := exists_valBar_ne_zero h τ
  have hpos : 0 < valBar F v (finEmb F v τ (a * u j)) := by
    rw [map_mul, map_mul]; exact mul_pos hpa (pos_iff_ne_zero.2 hj)
  obtain ⟨t, ht⟩ := exists_lt_nnnorm v (valBar F v (finEmb F v τ (a * u j)))⁻¹
  have h1 := mem_intLoc_iff_valBar.1
    (hc (t • a) (fun j => by rw [mul_smul_comm, ha, smul_zero, zero_mul]; exact zero_mem _) j) τ
  rw [smul_mul_assoc, valBar_smul, ← le_mul_inv_iff₀ hpos, one_mul] at h1
  exact absurd h1 (not_le.2 ht)

theorem smul_mem_latLoc_iff {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsFullLattice E L)
    {w l : Fin n → Fv F v ⊗[F] E} (h : l ⬝ᵥ w = 1) {c : Fv F v ⊗[F] E}
    (hc : ∀ a : Fv F v ⊗[F] E, (c * a) • w ∈ latLoc F L v ↔ a • w ∈ latLoc F L v) (y : Fin n → Fv F v ⊗[F] E) :
    y ∈ latLoc F L v ↔ c • y ∈ latLoc F L v := by
  obtain ⟨k, S, Φ, h1, hS, hΦ⟩ := SelfDual.exists_frame L hL
  have h2 := SelfDual.map_mul_eq_one (F := F) (Fv F v) h1
  set u := Φ.map (inclR (F := F) (Fv F v)) *ᵥ w with hu
  have hl : ∑ j, (l ᵥ* S.map (inclR (F := F) (Fv F v))) j * u j = 1 := by
    change (l ᵥ* _) ⬝ᵥ u = 1
    rw [← Matrix.dotProduct_mulVec, hu, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, h]
  have key : ∀ a : Fv F v ⊗[F] E, a • w ∈ latLoc F L v ↔ ∀ j, a * u j ∈ intLoc F E v := fun a => by
    rw [SelfDual.mem_latLoc_iff_of_frame h1 hS hΦ v, Matrix.mulVec_smul]
    rfl
  simp only [key] at hc
  have hc1 := mem_intLoc_of_stable hl fun a => (hc a).2
  obtain ⟨c, rfl⟩ := isUnit_of_reflect hl fun a => (hc a).1
  have hc2 : ((c⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ intLoc F E v :=
    mem_intLoc_of_stable hl fun a ha => (hc _).1 fun j => by rw [Units.mul_inv_cancel_left]; exact ha j
  refine ⟨fun hy => (latLoc F L v).smul_mem ⟨_, hc1⟩ hy, fun hy => ?_⟩
  have := (latLoc F L v).smul_mem ⟨_, hc2⟩ hy
  change ((c⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) • (c : Fv F v ⊗[F] E) • y ∈ _ at this
  rwa [smul_smul, Units.inv_mul, one_smul] at this

end Local



theorem smul_mem_latV_iff : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (Λ : GlobalTheory.FinPl.Lat V), Submodule.IsFullLattice D.host.E Λ → ∀ (v : GlobalTheory.FinPl.Pl D) (ε : Fin V.rank → D.host.E), ε ≠ 0 → ∀ (c : AE D) (s : Matrix (Fin V.rank) (Fin V.rank) (AE D)), IsUnit s → (∀ a ∈ GlobalTheory.FinPl.idAt D (· = v), (Matrix.mulVec (s) (fun i => c * (a * Formalism.L2.Theta.incA D (ε i))) ∈ GlobalTheory.FinPl.latV V Λ (· = v) ↔ Matrix.mulVec (s) (fun i => a * Formalism.L2.Theta.incA D (ε i)) ∈ GlobalTheory.FinPl.latV V Λ (· = v))) → ∀ y : Fin V.rank → AE D, (∀ i, y i ∈ GlobalTheory.FinPl.idAt D (· = v)) → (y ∈ GlobalTheory.FinPl.latV V Λ (· = v) ↔ c • y ∈ GlobalTheory.FinPl.latV V Λ (· = v)) := by
  intro D V Λ hΛ v ε hε c s hs h y hy
  have hfg : Λ.FG := by
    letI := hΛ
    exact Submodule.IsLattice.fg D.host.E Λ
  let π : AE D →+* Fv D.host.F v ⊗[D.host.F] D.host.E := (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v).comp (finPart D)
  have hπ : ∀ z : Fin V.rank → AE D, (∀ i, z i ∈ GlobalTheory.FinPl.idAt D (· = v)) →
      (z ∈ GlobalTheory.FinPl.latV V Λ (· = v) ↔ (fun i => π (z i)) ∈ latLoc D.host.F Λ v) := fun z hz =>
    GlobalTheory.StMoves.mem_latV_iff_latLoc V Λ hfg v z hz
  let w : Fin V.rank → AE D := s *ᵥ fun i => Formalism.L2.Theta.incA D (ε i)
  have hw : ∀ a : AE D, (s *ᵥ fun i => a * Formalism.L2.Theta.incA D (ε i)) = a • w := fun a =>
    Matrix.mulVec_smul s a _
  obtain ⟨l, hl⟩ : ∃ l : Fin V.rank → AE D, l ⬝ᵥ w = 1 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hε
    obtain ⟨s', rfl⟩ := hs
    refine ⟨(Pi.single i (Formalism.L2.Theta.incA D (ε i)⁻¹)) ᵥ* (s'⁻¹).1, ?_⟩
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, single_dotProduct,
      ← map_mul, inv_mul_cancel₀ hi, map_one]
  have hl' : (fun i => π (l i)) ⬝ᵥ (fun i => π (w i)) = 1 := by
    rw [← map_one π, ← hl]

    simp only [dotProduct, map_sum, map_mul]
  have hsm : ∀ (a : AE D) (z : Fin V.rank → AE D), (fun i => π ((a • z) i)) = π a • fun i => π (z i) :=
    fun a z => funext fun i => map_mul π a (z i)
  rw [hπ y hy, hπ (c • y) fun i => Ideal.mul_mem_left _ _ (hy i), hsm]
  refine smul_mem_latLoc_iff Λ hΛ hl' (fun b => ?_) _
  obtain ⟨a, ha, hab⟩ := GlobalTheory.StMoves.exists_supp_vecLoc_eq (D := D) (n := 1) v fun _ => b
  have hab' : π (a 0) = b := congrFun hab 0
  have h1 := h (a 0) (ha 0)
  simp only [← mul_assoc] at h1
  rw [hw, hw, hπ ((c * a 0) • w) fun i => Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (ha 0)),
    hπ (a 0 • w) fun i => Ideal.mul_mem_right _ _ (ha 0), hsm, hsm, map_mul, hab'] at h1
  exact h1

end GlobalTheory.LineUnit

end
end

section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
noncomputable section

namespace GlobalTheory.LineAtG



theorem mem_latLoc_line_iff {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (L : GlobalTheory.FinPl.Lat V) (hL : L.FG) (v : GlobalTheory.FinPl.Pl D) (t : GA D V)
    (ε : Fin V.rank → D.host.E) (y : AE D) (hy : y ∈ GlobalTheory.FinPl.idAt D (· = v)) :
    Matrix.mulVec ((GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig V.gram
        (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v t))⁻¹).val
        (GlobalTheory.AdelicU.vecLoc v (finPart D ∘ fun _ : Fin 1 => y) 0 • fun i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) ⊗ₜ[D.host.F] ε i) ∈
        GlobalTheory.AdelicU.latLoc D.host.F L v ↔
      Matrix.mulVec (Formalism.L2.Theta.mt V t⁻¹) (fun i => y * Formalism.L2.Theta.incA D (ε i)) ∈ GlobalTheory.FinPl.latV V L (· = v) := by
  have hy' : ∀ i, (fun i => y * Formalism.L2.Theta.incA D (ε i)) i ∈ GlobalTheory.FinPl.idAt D (· = v) := fun i => Ideal.mul_mem_right _ _ hy
  rw [GlobalTheory.StMoves.mem_latV_iff_latLoc V L hL v _ (GlobalTheory.FinPl.KOpen.supp_mulVec V _ t⁻¹ hy'), GlobalTheory.FinPl.KOpen.fin_mulVec,
    GlobalTheory.AdelicU.vecLoc_mulVec, map_inv, map_inv]
  have hv : GlobalTheory.AdelicU.vecLoc v (finPart D ∘ fun i => y * Formalism.L2.Theta.incA D (ε i)) =
      GlobalTheory.AdelicU.vecLoc v (finPart D ∘ fun _ : Fin 1 => y) 0 • fun i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) ⊗ₜ[D.host.F] ε i := by
    funext i
    simp only [Function.comp, GlobalTheory.AdelicU.vecLoc, Pi.smul_apply, smul_eq_mul, map_mul]
    congr 1
  rw [hv]


end GlobalTheory.LineAtG
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.SplitTransfer

theorem seg_map_inv {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : ℂˣ) (t : ℕ) :
    (GlobalTheory.LFun.seg w x t).map (·⁻¹) = GlobalTheory.LFun.seg w x⁻¹ t := by
  have hr : (Finset.range t).image (fun i => t - 1 - i) = Finset.range t := by
    ext i
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩; omega
    · intro hi; exact ⟨t - 1 - i, by omega, by omega⟩
  have hinj : Set.InjOn (fun i => t - 1 - i) (Finset.range t : Set ℕ) := fun a ha b hb e => by
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    simp only at e
    omega
  unfold GlobalTheory.LFun.seg
  conv_rhs => rw [← hr, Finset.image_val_of_injOn hinj, Multiset.map_map]
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl fun i hi => ?_
  have hi' : i < t := Finset.mem_range.1 hi
  simp only [Function.comp_apply, mul_inv]
  congr 1
  apply Units.ext
  simp only [Units.val_inv_eq_inv_val, GlobalTheory.LFun.coe_npowU, GlobalTheory.LFun.npow]
  rw [← Complex.cpow_neg]
  congr 1
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring



theorem transferOn_isSplit : ∀ D : D7, TransferOn D fun v => IsSplit (E := D.host.E) v := by
  intro D ψ S T χS χT om hW t ht v hv hunr w h U hU f hf X _ _ ρ x B hx X' _ _ ρ' b hb hne
  obtain ⟨eS, heS⟩ := (GlobalTheory.T.exists_unitaryCharts_allFinitePlaces_frameLattice D S v w h).1 hv
  obtain ⟨eT, heT⟩ := (GlobalTheory.T.exists_unitaryCharts_allFinitePlaces_frameLattice D T v w h).1 hv
  have hxS := hx.isSatVecGL hv heS
  obtain ⟨hfix, hH⟩ := GlobalTheory.T.latticeVacuum_heckeIdentity_splitPlace_charts D ψ S T χS χT om hW t ht v w h hv hunr eS eT heS heT (f : WO S T → ℂ) hf
  obtain ⟨hcS, hsS⟩ := GlobalTheory.T.integral_GL_commensurated_doubleCosetCardInvSymm D.host.E w S.rank
  obtain ⟨hcT, hsT⟩ := GlobalTheory.T.integral_GL_commensurated_doubleCosetCardInvSymm D.host.E w T.rank
  let σF : Representation ℂ (GL (Fin S.rank) (w.adicCompletion D.host.E)) (WO S T → ℂ) :=
    ((om.comp (MonoidHom.inl _ _)).comp (embV S v)).comp eS.symm.toMonoidHom
  let πF : Representation ℂ (GL (Fin T.rank) (w.adicCompletion D.host.E)) (WO S T → ℂ) :=
    ((om.comp (MonoidHom.inr _ _)).comp (embV T v)).comp eT.symm.toMonoidHom
  have eσ : ∀ g, σF g = om (embV S v (eS.symm g), embV T v 1) := fun g => by simp [σF]
  have eπ : ∀ g, πF g = om (embV S v 1, embV T v (eT.symm g)) := fun g => by simp [πF]
  let σU := σF.subrepresentation U fun g u hu => by rw [Submodule.mem_comap, eσ]; exact hU _ _ u hu
  let πU := πF.subrepresentation U fun g u hu => by rw [Submodule.mem_comap, eπ]; exact hU _ _ u hu
  let ρS := ρ.comp eS.symm.toMonoidHom
  let ρT := ρ'.comp eT.symm.toMonoidHom

  have hKS : ∀ k ∈ KGL w (n := S.rank), eS.symm k ∈ Kv S v := fun k hk => (heS.2 (eS.symm k)).2 (by simpa using hk)
  have hKT : ∀ k ∈ KGL w (n := T.rank), eT.symm k ∈ Kv T v := fun k hk => (heT.2 (eT.symm k)).2 (by simpa using hk)
  have hfS : f ∈ fixed σU (KGL w (n := S.rank)) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (by
    change σF k (f : WO S T → ℂ) = f
    rw [eσ]; exact hfix _ (hKS k hk) _ (one_mem _))
  have hfT : f ∈ fixed πU (KGL w (n := T.rank)) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (by
    change πF k (f : WO S T → ℂ) = f
    rw [eπ]; exact hfix _ (one_mem _) _ (hKT k hk))
  have hequiv : ∀ g (u : U), (b.flip x) (πU g u) = ρT g ((b.flip x) u) := fun g u => by
    have e := hb 1 (eT.symm g) u x
    rw [show ρ 1 x = x by simp] at e
    rw [LinearMap.flip_apply, LinearMap.flip_apply]
    change b (πU g u) x = ρ' (eT.symm g) (b u x)
    rw [← e]
    congr 2
    exact Subtype.ext (by change πF g (u : WO S T → ℂ) = _; rw [eπ])
  have hinv : ∀ g (u : U) y, b (σU g u) (ρS g y) = b u y := fun g u y => by
    have e := hb (eS.symm g) 1 u y
    rw [show ρ' 1 (b u y) = b u y by simp] at e
    rw [← e]
    congr 2
    exact Subtype.ext (by change σF g (u : WO S T → ℂ) = _; rw [eσ])
  have hbfix : b f x ∈ fixed ρT (KGL w (n := T.rank)) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
    have e := hequiv k f
    rw [GlobalTheory.LGrp.mem_fixed.1 hfT k hk] at e
    exact e.symm
  have hcard : (stepPar χS χT t (fun _ => B) w).card = T.rank := by
    simp [stepPar, GlobalTheory.LFun.seg, hxS.2.2.1, ht]
  have hB'inv : (stepPar χS χT t (fun _ => B) w).map (·⁻¹) =
      (B.map (·⁻¹)).map ((val (F := D.host.F) χS w)⁻¹ * ((val (F := D.host.F) χT w)⁻¹)⁻¹ * ·) +
        GlobalTheory.LFun.seg w (val (F := D.host.F) χS w)⁻¹ t := by
    rw [stepPar, Multiset.map_add (f := _), seg_map_inv, Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun c _ => ?_
    simp only [Function.comp_apply, mul_inv]
  refine Or.inl ⟨hv, eT, heT, (GlobalTheory.T.satake_vector_iff_inverse_doubleCosets D.host.E w T.rank X' ρT (b f x) _ hne hbfix hcard).2 fun ϖ hϖ k hk => ?_⟩
  have hsubT : ∀ g (y : U), U.subtype (πU g y) = πF g (U.subtype y) := fun g y => rfl
  have hsubS : ∀ g (y : U), U.subtype (σU g y) = σF g (U.subtype y) := fun g y => rfl
  have hInvT : (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) ∈ Hecke ℂ (KGL w (n := T.rank)) :=
    (GlobalTheory.T.hecke_operator_move_across_invariant_bilinear _ (KGL w (n := T.rank)) hcT hsT ℂ ℂ ℂ 1 1 0 (fun _ _ _ => by simp) 0 (zero_mem _) 0 (zero_mem _) _
      (Tj_mem_hecke hϖ k)).1
  let cf : ℕ → ℂ := fun j => if j ≤ k then (qV D.host.E w : ℂ) ^ ((S.rank - j) * (k - j)) *
    (Formalism.L2.Col.gaussBin (qV D.host.E w) t (k - j) : ℂ) *
    (((val (F := D.host.F) χS w : ℂˣ) : ℂ) * (Real.sqrt (qV D.host.E w) : ℂ) ^ S.rank)⁻¹ ^ k *
    (((val (F := D.host.F) χT w : ℂˣ) : ℂ) * (Real.sqrt (qV D.host.E w) : ℂ) ^ T.rank) ^ j else 0
  have hH' : heckeVec πF (KGL w (n := T.rank)) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) (U.subtype f) =
      ∑ j ∈ Finset.range (S.rank + 1), cf j • heckeVec σF (KGL w (n := S.rank)) (Tj ℂ S.rank (Ov D.host.E w) ϖ j) (U.subtype f) :=
    hH ϖ hϖ k hk
  have e1 : U.subtype (heckeVec πU (KGL w (n := T.rank)) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) f) =
      heckeVec πF (KGL w (n := T.rank)) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) (U.subtype f) :=
    map_heckeVec hcT hInvT U.subtype hsubT f
  have e2 : ∀ j, U.subtype (heckeVec σU (KGL w (n := S.rank)) (Tj ℂ S.rank (Ov D.host.E w) ϖ j) f) =
      heckeVec σF (KGL w (n := S.rank)) (Tj ℂ S.rank (Ov D.host.E w) ϖ j) (U.subtype f) := fun j =>
    map_heckeVec hcS (Tj_mem_hecke hϖ j) U.subtype hsubS f
  have hT : heckeVec πU (KGL w (n := T.rank)) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) f =
      ∑ j ∈ Finset.range (S.rank + 1), cf j • heckeVec σU (KGL w (n := S.rank)) (Tj ℂ S.rank (Ov D.host.E w) ϖ j) f := by
    apply U.injective_subtype

    rw [e1, hH', map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, e2 j]
  have hmove : ∀ j ∈ Finset.range (S.rank + 1), b (heckeVec σU (KGL w (n := S.rank)) (Tj ℂ S.rank (Ov D.host.E w) ϖ j) f) x =
      satEig (qV D.host.E w) S.rank (B.map (·⁻¹)) j • b f x := by
    intro j hj
    rw [(GlobalTheory.T.hecke_operator_move_across_invariant_bilinear _ _ hcS hsS U X X' σU ρS b hinv f hfS x hxS.2.1 _ (Tj_mem_hecke hϖ j)).2,
      (GlobalTheory.T.satake_vector_iff_inverse_doubleCosets D.host.E w S.rank X ρS x B hxS.1 hxS.2.1 hxS.2.2.1).1 hxS ϖ hϖ j
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)), map_smul]
  have hsym := GlobalTheory.T.satake_esymm_scaled_multiset_add_segment D.host.E w S.rank t k (B.map (·⁻¹)) (val (F := D.host.F) χS w)⁻¹
    (val (F := D.host.F) χT w)⁻¹ (by rw [Multiset.card_map, hxS.2.2.1]) (ht ▸ hk)
  calc heckeVec ρT (KGL w (n := T.rank)) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) (b f x)
      = b (heckeVec πU (KGL w (n := T.rank)) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) f) x :=
        (map_heckeVec hcT hInvT (b.flip x) hequiv f).symm
    _ = ∑ j ∈ Finset.range (S.rank + 1), cf j • satEig (qV D.host.E w) S.rank (B.map (·⁻¹)) j • b f x := by

        rw [hT, map_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [map_smul, LinearMap.smul_apply, hmove j hj]
    _ = satEig (qV D.host.E w) T.rank ((stepPar χS χT t (fun _ => B) w).map (·⁻¹)) k • b f x := by
        simp_rw [smul_smul]
        rw [← Finset.sum_smul]
        congr 1
        rw [hB'inv, ht, hsym]
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        simp only [cf]
        split_ifs
        · rw [ht]
          simp only [Units.val_inv_eq_inv_val, inv_inv, mul_inv]
        · rfl

end GlobalTheory.ChainOnto.SplitTransfer
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.representative_diamond_translate_sum_scalarForm : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi j, ∀ (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 →
    ∀ g : 𝓀[k]ˣ → GL (Fin ((I.rec7 l Z).sp.X j).rank) k, (∀ s, g s • Q j i = s • Q j i) →
      ∀ b y (c : {c // A.chOf j c = b}), (∑ᶠ s, A.rd θ j hj b φ y (A.h j b c * (β j i).gl (g s))) = (∑ᶠ s : ((I.atT l u a).Fv v)ˣ, (I.fm l u a).dilT j v s c.1 (φ ((I.fm l u a).dil j v s c.1))) y := by
  first | exact @GlobalTheory.AdForm.rd_dia_sum | exact GlobalTheory.AdForm.rd_dia_sum | (intros; apply GlobalTheory.AdForm.rd_dia_sum <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.standardPair_stabiliser_mem_chartLevel : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ j, j ≤ B.R.m → ∀ b, ∀ i (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k), g • Q j i = Q j i → (β j i).gl g ∈ A.U j b := by
  first | exact @GlobalTheory.AdForm.StabLev.stab_mem_level | exact GlobalTheory.AdForm.StabLev.stab_mem_level | (intros; apply GlobalTheory.AdForm.StabLev.stab_mem_level <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.trueColumns_realData_spec : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → IsEmbTop (D := (I.rec7 l Z)) (TC.z0 X u) ((g.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _)) → (realOf u R g s J).Is := by
  first | exact @GlobalTheory.AdForm.realOf_is | exact GlobalTheory.AdForm.realOf_is | (intros; apply GlobalTheory.AdForm.realOf_is <;> assumption)
end

section


theorem _root_.GlobalTheory.T.twistFiniteDatum_theta_at_levelPrime : GlobalTheory.AdForm.TwVec' := by
  first | exact @GlobalTheory.AdForm.twVec' | exact GlobalTheory.AdForm.twVec' | (intros; apply GlobalTheory.AdForm.twVec' <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.indexZeroLevel_generated_by_local_unipotents : ∀ {D : D7} {c : Comm D} {v : VCom c} (cm : GlobalTheory.ChainOnto.Com D) (st : StAt (c.V 0)) (b : GA D (c.V 0)) (G : cm.Pg → GLoc v) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), GlobalTheory.LevZero.Bot cm st b G → ∀ Q : GA D (c.V 0) → Prop, (∀ k ∈ levS (c.V 0) st.β st.L, ∀ k' ∈ levS (c.V 0) st.β st.L, Q k → Q k' → Q (k * k')) → (∀ (PP : cm.Pg) (n : GA D (c.V 0)) (q : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin ((G PP).s + 1)) (G PP).k), n ∈ flagN (c.bes 0 D.R.rS h0).d → q ∈ GlobalTheory.RootEx.N (G PP).k _ ((G PP).s + 1) (D.R.rS + 1) → (ofSplit (G PP).q).IsLoc ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _)) n q → b⁻¹ * n * b ∈ levS (c.V 0) st.β st.L → Q (b⁻¹ * n * b)) → (∀ x ∈ GfC (c.X 0), b⁻¹ * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o x * b ∈ levS (c.V 0) st.β st.L → Q (b⁻¹ * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o x * b)) → (∀ k ∈ levS (c.V 0) st.β st.L, (∀ PP ∈ cm.Pg, redFn st.β PP (finE (c.V 0) k) = 1) → Q k) → ∀ k ∈ levS (c.V 0) st.β st.L, Q k := by
  first | exact @GlobalTheory.LevZero.gen | exact GlobalTheory.LevZero.gen | (intros; apply GlobalTheory.LevZero.gen <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_lastPeriod_classData_of_lastStep : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∃ E : ClsT (realOf u R g s J) (tupOf R P u g t r k tl), E.Is := by
  first | exact @GlobalTheory.AdForm.exists_clsT_of_pinTop | exact GlobalTheory.AdForm.exists_clsT_of_pinTop | (intros; apply GlobalTheory.AdForm.exists_clsT_of_pinTop <;> assumption)
end
