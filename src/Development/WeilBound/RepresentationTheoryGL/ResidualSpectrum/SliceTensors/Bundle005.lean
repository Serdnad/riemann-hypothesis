module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle004
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle004
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle620
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle119
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle132
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle488
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle536
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermLeviParabolicFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericFiniteByInduction
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

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs.ChordArithmetic

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem mulChi_absC_cancel (a : ℕ) (z : ℂ) (ψ : Sm E a) :
    mulChi a (Model.absC E z) (mulChi a (Model.absC E (-z)) ψ) = ψ := by
  refine Subtype.ext (funext fun m => ?_)
  rw [mulChi_apply, mulChi_apply, ExponentTwist.chiDet_absC_val, ExponentTwist.chiDet_absC_val, mul_assoc, ← Complex.exp_add]
  simp

theorem central_twist {a : ℕ} (w e : ℂ) (h : e + w * a * (Module.finrank ℚ E : ℂ) = 0) (ψ : Sm E a)
    (hψ : ∀ (t : ℝ) m, ψ.1 (splitCentre E a t * m) = Complex.exp (e * t) * ψ.1 m) :
    ∀ (t : ℝ) m, (mulChi a (Model.absC E w) ψ).1 (splitCentre E a t * m) = (mulChi a (Model.absC E w) ψ).1 m := by
  intro t m
  rw [mulChi_apply, mulChi_apply, map_mul, Units.val_mul, hψ, ExponentTwist.splitCentre_eq, ExponentTwist.chiDet_aT le_rfl]
  have e1 : Complex.exp (e * t) * Complex.exp (w * a * (Module.finrank ℚ E : ℂ) * t) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    linear_combination (t : ℂ) * h
  linear_combination (ψ.1 m * ((chiDet a (Model.absC E w) m : ℂˣ) : ℂ)) * e1

theorem left_eq (c c₁ : ℂ) (r r₁ d : ℕ) (hr : r ≠ 0) (hd : d ≠ 0) :
    (c₁ - -(c / (r * d)) * r₁ * d).re = c₁.re + (r₁ : ℝ) / r * c.re := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have e : c₁ - -(c / (r * d)) * r₁ * d = c₁ + (((r₁ : ℝ) / r : ℝ) : ℂ) * c := by
    push_cast
    field_simp
    ring
  rw [e, Complex.add_re, Complex.re_ofReal_mul]

theorem right_eq (c c₂ : ℂ) (s r₂ d : ℕ) (hs : s ≠ 0) (hd : d ≠ 0) :
    (c + (c₂ - -(-c / (s * d)) * r₂ * d)).re = c₂.re + ((s : ℝ) - r₂) / s * c.re := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have e : c + (c₂ - -(-c / (s * d)) * r₂ * d) = c₂ + ((((s : ℝ) - r₂) / s : ℝ) : ℂ) * c := by
    push_cast
    field_simp
    ring
  rw [e, Complex.add_re, Complex.re_ofReal_mul]

theorem left_arith (r s r₁ d lam x y : ℝ) (hr : 0 < r) (h1 : 0 < r₁) (h2 : r₁ < r) (hlam : 0 < lam)
    (hp : y / d - r * (r + s - r) / 2 = -lam * (r * s))
    (hb : (x + r₁ / r * y) / d - r₁ * (r + s - r₁) / 2 ≤ -lam * (r₁ * (r + s - r₁))) :
    x / d - r₁ * (r - r₁) / 2 < 0 := by
  have hY : y / d = r * s / 2 - lam * (r * s) := by linarith
  have e : (x + r₁ / r * y) / d = x / d + r₁ / r * (y / d) := by ring
  have e2 : r₁ / r * (r * s / 2 - lam * (r * s)) = r₁ * s / 2 - lam * (r₁ * s) := by field_simp
  rw [e, hY, e2] at hb
  nlinarith [mul_pos hlam (mul_pos h1 (sub_pos.2 h2))]

theorem right_arith (r s r₂ d lam x y : ℝ) (hs : 0 < s) (h1 : 0 < r₂) (h2 : r₂ < s) (hlam : 0 < lam)
    (hp : y / d - r * (r + s - r) / 2 = -lam * (r * s))
    (hb : (x + (s - r₂) / s * y) / d - (r + r₂) * (r + s - (r + r₂)) / 2 ≤ -lam * ((r + r₂) * (r + s - (r + r₂)))) :
    x / d - r₂ * (s - r₂) / 2 < 0 := by
  have hY : y / d = r * s / 2 - lam * (r * s) := by linarith
  have e : (x + (s - r₂) / s * y) / d = x / d + (s - r₂) / s * (y / d) := by ring
  have e2 : (s - r₂) / s * (r * s / 2 - lam * (r * s)) = r * (s - r₂) / 2 - lam * (r * (s - r₂)) := by
    field_simp
  rw [e, hY, e2] at hb
  nlinarith [mul_pos hlam (mul_pos h1 (sub_pos.2 h2))]

end PositivityTheory.Rg.Rs.ChordArithmetic
end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin GlobalTheory.BCWords

namespace PositivityTheory.Rg.Rs.PInfInd2A

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem tensorSp_levi {n : Fin 2 → ℕ} (h : ∑ i, n i = n 0 + n 1) (W₁ : Submodule ℂ (Sm E (n 0)))
    (W₂ : Submodule ℂ (Sm E (n 1))) (ψ : Sm E (n 0 + n 1))
    (hψ : (fun p => ψ.1 (lev (Ad E) (n 0) (n 1) p)) ∈ tens2 W₁ W₂) :
    (fun m => ψ.1 (leviEmb (Ad E) (stdBlocks n h) m)) ∈ tensorSp (blkV W₁ W₂) := by
  have := tensorSp_of_tens2 W₁ W₂ hψ
  convert this using 2 with m
  rw [CapFactor.lev_eq_leviEmb n h, levPair_eta]

theorem capR_lev {n : Fin 2 → ℕ} (W₁ : Submodule ℂ (Sm E (n 0))) (W₂ : Submodule ℂ (Sm E (n 1))) (τ : E →+* ℂ)
    (M : Multiset ℂ) (hM : HasInfCharGL W₁ τ M) (w : ℂ) (ψ : Sm E (n 0 + n 1))
    (hψ : (fun p => ψ.1 (lev (Ad E) (n 0) (n 1) p)) ∈ tens2 W₁ W₂) (p : GA E (n 0) × GA E (n 1)) :
    (capR (n 0) (n 1) τ w ψ).1 (lev (Ad E) (n 0) (n 1) p) = (M.map (w + ·)).prod * ψ.1 (lev (Ad E) (n 0) (n 1) p) := by
  have h : ∑ i, n i = n 0 + n 1 := CapFactor.two_sum n
  have key := GlobalTheory.NormIndCap.qdet_block_levi n h (blkV W₁ W₂) τ 0 M hM w ψ (tensorSp_levi h W₁ W₂ ψ hψ)
    (CapFactor.levPair p)
  have e1 : (fun p q : Fin (n 0) => Eop (a := n 0 + n 1) τ (stdBlocks n h ⟨0, p⟩) (stdBlocks n h ⟨0, q⟩)) =
      fun p q => Eop (a := n 0 + n 1) τ (Fin.castAdd (n 1) p) (Fin.castAdd (n 1) q) := by
    funext p q
    rw [CapFactor.std_zero, CapFactor.std_zero]
  rw [e1, ← CapFactor.lev_eq_leviEmb n h] at key
  exact key

theorem capS_lev {n : Fin 2 → ℕ} (W₁ : Submodule ℂ (Sm E (n 0))) (W₂ : Submodule ℂ (Sm E (n 1))) (τ : E →+* ℂ)
    (M : Multiset ℂ) (hM : HasInfCharGL W₂ τ M) (w : ℂ) (ψ : Sm E (n 0 + n 1))
    (hψ : (fun p => ψ.1 (lev (Ad E) (n 0) (n 1) p)) ∈ tens2 W₁ W₂) (p : GA E (n 0) × GA E (n 1)) :
    (capS (n 0) (n 1) τ w ψ).1 (lev (Ad E) (n 0) (n 1) p) = (M.map (w + ·)).prod * ψ.1 (lev (Ad E) (n 0) (n 1) p) := by
  have h : ∑ i, n i = n 0 + n 1 := CapFactor.two_sum n
  have key := GlobalTheory.NormIndCap.qdet_block_levi n h (blkV W₁ W₂) τ 1 M hM w ψ (tensorSp_levi h W₁ W₂ ψ hψ)
    (CapFactor.levPair p)
  have e1 : (fun p q : Fin (n 1) => Eop (a := n 0 + n 1) τ (stdBlocks n h ⟨1, p⟩) (stdBlocks n h ⟨1, q⟩)) =
      fun p q => Eop (a := n 0 + n 1) τ (Fin.natAdd (n 0) p) (Fin.natAdd (n 0) q) := by
    funext p q
    rw [CapFactor.std_one, CapFactor.std_one]
  rw [e1, ← CapFactor.lev_eq_leviEmb n h] at key
  exact key

theorem casimir_on_parabolic_induction {n : Fin 2 → ℕ} (W₁ : Submodule ℂ (Sm E (n 0))) (W₂ : Submodule ℂ (Sm E (n 1))) (τ : E →+* ℂ)
    (M₁ M₂ : Multiset ℂ) (h₁ : HasInfCharGL W₁ τ M₁) (h₂ : HasInfCharGL W₂ τ M₂) (u : ℂ) (F : Sm E (n 0 + n 1))
    (hF : MemInd2 W₁ W₂ F) :
    cap τ u F = ((M₁.map (u - (n 1 : ℂ) / 2 + ·)).prod * (M₂.map (u + (n 0 : ℂ) / 2 + ·)).prod) • F := by
  have h : ∑ i, n i = n 0 + n 1 := CapFactor.two_sum n
  set c := (M₁.map (u - (n 1 : ℂ) / 2 + ·)).prod * (M₂.map (u + (n 0 : ℂ) / 2 + ·)).prod with hc
  have hlev : ∀ ψ : Sm E (n 0 + n 1), (∀ (x : BlockIx (n 0 + n 1) (n 0) → Ad E) g, ψ.1 (unip x * g) = ψ.1 g) →
      (fun p => ψ.1 (lev (Ad E) (n 0) (n 1) p)) ∈ tens2 W₁ W₂ → ∀ p,
      (cap τ u ψ).1 (lev (Ad E) (n 0) (n 1) p) = c * ψ.1 (lev (Ad E) (n 0) (n 1) p) := by
    intro ψ hψ hT p
    rw [CapFactor.cap_levi E (n 0) (n 1) τ u ψ hψ p]
    have hT' : (fun p => (capR (n 0) (n 1) τ (u - (n 1 : ℂ) / 2) ψ).1 (lev (Ad E) (n 0) (n 1) p)) ∈ tens2 W₁ W₂ := by
      have e : (fun p => (capR (n 0) (n 1) τ (u - (n 1 : ℂ) / 2) ψ).1 (lev (Ad E) (n 0) (n 1) p)) =
          (M₁.map (u - (n 1 : ℂ) / 2 + ·)).prod • (fun p => ψ.1 (lev (Ad E) (n 0) (n 1) p)) :=
        funext fun p => capR_lev W₁ W₂ τ M₁ h₁ _ ψ hT p
      rw [e]
      exact Submodule.smul_mem _ _ hT
    rw [capS_lev W₁ W₂ τ M₂ h₂ _ _ hT' p, capR_lev W₁ W₂ τ M₁ h₁ _ ψ hT p, hc]
    ring
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨v, hv, m, k, g, rfl⟩ := GlobalTheory.SpehInfChar.exists_iwasawa E n h x
  obtain ⟨xv, rfl⟩ := CapFactor.exists_unip_of_mem n h hv
  have hx : leviEmb (Ad E) (stdBlocks n h) m = lev (Ad E) (n 0) (n 1) (m 0, m 1) := by
    rw [CapFactor.lev_eq_leviEmb n h, levPair_eta]
  rw [hx]
  set y := infGL E (n 0 + n 1) (Unitary.toUnits k) * finGL E (n 0 + n 1) g
  have hcomm : Commute (cap τ u) (rt E (n 0 + n 1) y) := by
    rw [map_mul]
    exact (GlobalTheory.CapAdInv.cap_commute_rt_infGL E _ τ u _).mul_right (commute_cap_finRep τ u g)
  set ψ := rt E (n 0 + n 1) y F
  have hψ : ∀ (x : BlockIx (n 0 + n 1) (n 0) → Ad E) g', ψ.1 (unip x * g') = ψ.1 g' := fun x g' => by
    simp only [ψ, rt_apply, mul_assoc]
    exact hF.1 x _
  have hψT : (fun p => ψ.1 (lev (Ad E) (n 0) (n 1) p)) ∈ tens2 W₁ W₂ := hF.2 k g
  have h3 := hlev ψ hψ hψT (m 0, m 1)
  have h4 : (cap τ u ψ).1 (lev (Ad E) (n 0) (n 1) (m 0, m 1)) =
      (cap τ u F).1 (lev (Ad E) (n 0) (n 1) (m 0, m 1) * y) := by
    rw [← rt_apply, ← Module.End.mul_apply, hcomm.eq]
    rfl
  have hcapInv := (CapStable.capStable E (n 0) (n 1) τ u F).2 hF.1
  rw [mul_assoc, hcapInv, ← h4, h3]
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, ψ, rt_apply]
  rw [hF.1]

end PositivityTheory.Rg.Rs.PInfInd2A

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin
open scoped ContDiff

namespace PositivityTheory.Rg.Rs.InducedTensorMap

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}

namespace B

variable {R : Type} [CommRing R]

theorem lev_cc (m : GL (Fin r) R × GL (Fin s) R) (i j : Fin r) :
    (lev R r s m : Matrix (Fin (r + s)) (Fin (r + s)) R) (Fin.castAdd s i) (Fin.castAdd s j) = (m.1 : Matrix _ _ R) i j := by
  have h : (GlobalTheory.SmGL.emb₂ R (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) m).val =
      Matrix.reindex (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))
        (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))
        (Matrix.fromBlocks m.1.val 0 0 m.2.val) := by
    ext i j
    simp [GlobalTheory.SmGL.emb₂, GlobalTheory.SmGL.leviEmb, GlobalTheory.SmGL.leviTwo,
      GlobalTheory.SmGL.two, Matrix.reindex_apply, Matrix.blockDiagonal']
    rcases (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i with a | a <;>
      rcases (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j with b | b <;> simp
  rw [lev, h]
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, GlobalTheory.SmGL.stdSum]

theorem lev_nn (m : GL (Fin r) R × GL (Fin s) R) (i j : Fin s) :
    (lev R r s m : Matrix (Fin (r + s)) (Fin (r + s)) R) (Fin.natAdd r i) (Fin.natAdd r j) = (m.2 : Matrix _ _ R) i j := by
  have h : (GlobalTheory.SmGL.emb₂ R (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) m).val =
      Matrix.reindex (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))
        (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))
        (Matrix.fromBlocks m.1.val 0 0 m.2.val) := by
    ext i j
    simp [GlobalTheory.SmGL.emb₂, GlobalTheory.SmGL.leviEmb, GlobalTheory.SmGL.leviTwo,
      GlobalTheory.SmGL.two, Matrix.reindex_apply, Matrix.blockDiagonal']
    rcases (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i with a | a <;>
      rcases (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j with b | b <;> simp
  rw [lev, h]
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, GlobalTheory.SmGL.stdSum]

theorem lev_cn (m : GL (Fin r) R × GL (Fin s) R) (i : Fin r) (j : Fin s) :
    (lev R r s m : Matrix (Fin (r + s)) (Fin (r + s)) R) (Fin.castAdd s i) (Fin.natAdd r j) = 0 := by
  have h : (GlobalTheory.SmGL.emb₂ R (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) m).val =
      Matrix.reindex (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))
        (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))
        (Matrix.fromBlocks m.1.val 0 0 m.2.val) := by
    ext i j
    simp [GlobalTheory.SmGL.emb₂, GlobalTheory.SmGL.leviEmb, GlobalTheory.SmGL.leviTwo,
      GlobalTheory.SmGL.two, Matrix.reindex_apply, Matrix.blockDiagonal']
    rcases (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i with a | a <;>
      rcases (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j with b | b <;> simp
  rw [lev, h]
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, GlobalTheory.SmGL.stdSum]

theorem lev_nc (m : GL (Fin r) R × GL (Fin s) R) (i : Fin s) (j : Fin r) :
    (lev R r s m : Matrix (Fin (r + s)) (Fin (r + s)) R) (Fin.natAdd r i) (Fin.castAdd s j) = 0 := by
  have h : (GlobalTheory.SmGL.emb₂ R (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) m).val =
      Matrix.reindex (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))
        (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))
        (Matrix.fromBlocks m.1.val 0 0 m.2.val) := by
    ext i j
    simp [GlobalTheory.SmGL.emb₂, GlobalTheory.SmGL.leviEmb, GlobalTheory.SmGL.leviTwo,
      GlobalTheory.SmGL.two, Matrix.reindex_apply, Matrix.blockDiagonal']
    rcases (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i with a | a <;>
      rcases (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j with b | b <;> simp
  rw [lev, h]
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, GlobalTheory.SmGL.stdSum]

theorem unip_col (x : BlockIx (r + s) r → R) (i : Fin (r + s)) (k : Fin r) :
    ((unip x : GL (Fin (r + s)) R) : Matrix _ _ R) i (Fin.castAdd s k) =
      (1 : Matrix (Fin (r + s)) (Fin (r + s)) R) i (Fin.castAdd s k) := by
  have := k.isLt
  rw [GlobalTheory.CompanionTheory.AffglAssembly.unip_eq_unipGL, GroundTheory.Automorphic.AutomorphicForm.coe_unipGL,
    GroundTheory.Automorphic.AutomorphicForm.unipMatrix, Matrix.add_apply, GroundTheory.Automorphic.AutomorphicForm.blockEntry_apply,
    dite_eq_right (fun h => by have := h.2; simp only [Fin.val_castAdd] at this; omega), add_zero]

theorem unip_row (x : BlockIx (r + s) r → R) (k : Fin s) (j : Fin (r + s)) :
    ((unip x : GL (Fin (r + s)) R) : Matrix _ _ R) (Fin.natAdd r k) j =
      (1 : Matrix (Fin (r + s)) (Fin (r + s)) R) (Fin.natAdd r k) j := by
  rw [GlobalTheory.CompanionTheory.AffglAssembly.unip_eq_unipGL, GroundTheory.Automorphic.AutomorphicForm.coe_unipGL,
    GroundTheory.Automorphic.AutomorphicForm.unipMatrix, Matrix.add_apply, GroundTheory.Automorphic.AutomorphicForm.blockEntry_apply,
    dite_eq_right (fun h => by have := h.1; simp only [Fin.val_natAdd] at this; omega), add_zero]

end B

open B

theorem unip_zero {R : Type} [CommRing R] {a r : ℕ} : unip (0 : BlockIx a r → R) = 1 := by
  rw [GlobalTheory.CompanionTheory.AffglAssembly.unip_eq_unipGL]
  exact GroundTheory.Automorphic.AutomorphicForm.unipGL_zero

theorem unip_lev_ll {R : Type} [CommRing R] (u : BlockIx (r + s) r → R) (m : GL (Fin r) R × GL (Fin s) R)
    (i : Fin s) (j : Fin r) :
    ((unip u * lev R r s m : GL (Fin (r + s)) R) : Matrix _ _ R) (Fin.natAdd r i) (Fin.castAdd s j) = 0 := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_add]
  have h : ∀ x : Fin r, Fin.natAdd r i ≠ Fin.castAdd s x := fun x h => by
    have := congrArg Fin.val h
    have := x.isLt
    simp only [Fin.val_natAdd, Fin.val_castAdd] at *
    omega
  simp [unip_row, lev_nc, lev_cc, Matrix.one_apply, h]

theorem unip_lev_cc {R : Type} [CommRing R] (u : BlockIx (r + s) r → R) (m : GL (Fin r) R × GL (Fin s) R)
    (i j : Fin r) :
    ((unip u * lev R r s m : GL (Fin (r + s)) R) : Matrix _ _ R) (Fin.castAdd s i) (Fin.castAdd s j) =
      (m.1 : Matrix _ _ R) i j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_add]
  simp [unip_col, lev_nc, lev_cc, Matrix.one_apply]

theorem unip_lev_nn {R : Type} [CommRing R] (u : BlockIx (r + s) r → R) (m : GL (Fin r) R × GL (Fin s) R)
    (i j : Fin s) :
    ((unip u * lev R r s m : GL (Fin (r + s)) R) : Matrix _ _ R) (Fin.natAdd r i) (Fin.natAdd r j) =
      (m.2 : Matrix _ _ R) i j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_add]
  simp [unip_row, lev_cn, lev_nn, Matrix.one_apply]

theorem lev_mul_unip {R : Type} [CommRing R] (m : GL (Fin r) R × GL (Fin s) R) (u : BlockIx (r + s) r → R) :
    ∃ v : BlockIx (r + s) r → R, lev R r s m * unip u = unip v * lev R r s m := by
  have h1 := GlobalTheory.CompanionTheory.CTFin.blockDiag_lev (R := R) m
  have h2 : GlobalTheory.CompanionTheory.CTFin.BlockDiag r ((lev R r s m)⁻¹).val := by
    rw [← map_inv]; exact GlobalTheory.CompanionTheory.CTFin.blockDiag_lev _
  refine ⟨(GlobalTheory.CompanionTheory.CTFin.conjE (lev R r s m) h1 h2).symm u, ?_⟩
  rw [GlobalTheory.CompanionTheory.CTFin.unip_mul_eq _ h1 h2, AddEquiv.apply_symm_apply]

theorem cf_mul (a : ℕ) (k k' : Kinf E a) (g g' : GL (Fin a) (Af E)) : cf a k g * cf a k' g' = cf a (k * k') (g * g') := by
  refine ga_ext ?_ ?_ <;> simp [cf]

theorem exists_decomp (x : GA E (r + s)) : ∃ (u : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s))
    (g : GL (Fin (r + s)) (Af E)), x = unip u * lev (Ad E) r s m * cf (r + s) k g := by
  obtain ⟨T, hT⟩ := GlobalTheory.CompanionTheory.CTFin.IwaAd.iwasawa_finite_cosets E r s ⊤ isOpen_univ
  obtain ⟨y, m, t, k, l, -, -, rfl⟩ := hT x
  refine ⟨y, m, k, t * l, ?_⟩
  rw [cf, map_mul, ← mul_assoc (infGL E (r + s) _), infGL_comm]
  simp only [mul_assoc]

theorem levi_cf {u : BlockIx (r + s) r → Ad E} {m : GA E r × GA E s} {k : Kinf E (r + s)} {g : GL (Fin (r + s)) (Af E)}
    (h : unip u * lev (Ad E) r s m = cf (r + s) k g) :
    ∃ (k₁ : Kinf E r) (g₁ : GL (Fin r) (Af E)) (k₂ : Kinf E s) (g₂ : GL (Fin s) (Af E)), m = (cf r k₁ g₁, cf s k₂ g₂) := by
  have h1 := congrArg (Matrix.GeneralLinearGroup.map (pInf E)) h
  rw [map_mul, GlobalTheory.CompanionTheory.CTFin.IwaAd.map_unip, GlobalTheory.CompanionTheory.CTFin.IwaAd.map_lev, cf, map_mul, pInf_infGL, pInf_finGL, mul_one] at h1
  set y₁ := Matrix.GeneralLinearGroup.map (pInf E) m.1 with hy₁
  set y₂ := Matrix.GeneralLinearGroup.map (pInf E) m.2 with hy₂
  have hv : ((Unitary.toUnits k : GL (Fin (r + s)) (Cinf E)) : Matrix _ _ _) = k.1 := rfl
  have hll : ∀ i j, k.1 (Fin.natAdd r i) (Fin.castAdd s j) = 0 := fun i j => by rw [← hv, ← h1, unip_lev_ll]
  have hcc : ∀ i j, k.1 (Fin.castAdd s i) (Fin.castAdd s j) = y₁.val i j := fun i j => by rw [← hv, ← h1, unip_lev_cc]
  have hnn : ∀ i j, k.1 (Fin.natAdd r i) (Fin.natAdd r j) = y₂.val i j := fun i j => by rw [← hv, ← h1, unip_lev_nn]
  have u₁ : y₁.val ∈ Matrix.unitaryGroup (Fin r) (Cinf E) := by
    rw [Matrix.mem_unitaryGroup_iff']
    ext1 i j
    have := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 k.2) (Fin.castAdd s i)) (Fin.castAdd s j)
    rw [Matrix.mul_apply, Fin.sum_univ_add] at this
    simp only [Matrix.star_apply, hll, hcc, mul_zero, Finset.sum_const_zero, add_zero, Matrix.one_apply,
      Fin.castAdd_inj] at this
    rw [Matrix.mul_apply, Matrix.one_apply, ← this]
    rfl
  have u₂ : y₂.val ∈ Matrix.unitaryGroup (Fin s) (Cinf E) := by
    rw [Matrix.mem_unitaryGroup_iff]
    ext1 i j
    have := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.1 k.2) (Fin.natAdd r i)) (Fin.natAdd r j)
    rw [Matrix.mul_apply, Fin.sum_univ_add] at this
    simp only [Matrix.star_apply, hll, hnn, zero_mul, Finset.sum_const_zero, zero_add, Matrix.one_apply,
      Fin.natAdd_inj] at this
    rw [Matrix.mul_apply, Matrix.one_apply, ← this]
    rfl
  refine ⟨⟨_, u₁⟩, Matrix.GeneralLinearGroup.map (pFin E) m.1, ⟨_, u₂⟩, Matrix.GeneralLinearGroup.map (pFin E) m.2,
    Prod.ext ?_ ?_⟩
  · exact (infGL_mul_finGL m.1).symm.trans (congrArg (fun z => infGL E r z * _) (Units.ext rfl))
  · exact (infGL_mul_finGL m.2).symm.trans (congrArg (fun z => infGL E s z * _) (Units.ext rfl))

theorem lev_mul_infGL (m : GA E r × GA E s) (u : BlockIx (r + s) r → Cinf E) (b₁ : GL (Fin r) (Cinf E))
    (b₂ : GL (Fin s) (Cinf E)) (κ : Kinf E (r + s)) :
    ∃ v : BlockIx (r + s) r → Ad E, lev (Ad E) r s m * infGL E (r + s) (unip u * lev (Cinf E) r s (b₁, b₂) * Unitary.toUnits κ) =
      unip v * lev (Ad E) r s (m.1 * infGL E r b₁, m.2 * infGL E s b₂) * cf (r + s) κ 1 := by
  have e : infGL E (r + s) (unip u) = unip fun p => sInf E (u p) := by
    refine ga_ext ?_ ?_
    · rw [pInf_infGL, GlobalTheory.CompanionTheory.CTFin.IwaAd.map_unip]
      congr 1
      funext p
      exact ((infEq E).symm_apply_apply _).symm
    · rw [pFin_infGL, GlobalTheory.CompanionTheory.CTFin.IwaAd.map_unip]
      exact unip_zero.symm
  obtain ⟨v, hv⟩ := lev_mul_unip m fun p => sInf E (u p)
  refine ⟨v, ?_⟩
  rw [map_mul, map_mul, e, ← GlobalTheory.CompanionTheory.CTFin.Slice1.lev_infGL, ← mul_assoc, ← mul_assoc, hv, cf, map_one, mul_one, mul_assoc (unip v),
    ← map_mul]
  rfl

end PositivityTheory.Rg.Rs.InducedTensorMap

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs

theorem expTw_holds : ExpTw := by
  intro E _ _ _ N φ z _ r _ hrN c hc
  let _ : MeasurableSpace (BlockIx N r → Ad E) := borel _
  obtain ⟨F₀, ⟨μ, 𝓕, hμ, h𝓕, hF₀⟩, F, hF, hF0, hFt⟩ := hc
  set χ := Model.absC E z
  set Y : GA E N → ℂ := fun g => (((chiDet N χ g)⁻¹ : ℂˣ) : ℂ) with hY
  have hu : ∀ (x : BlockIx N r → Ad E), chiDet N χ (unip x) = 1 := fun x => by
    change (χ : GlobalTheory.Mem.Chr.Ideles E →* ℂˣ) (Matrix.GeneralLinearGroup.det (unip x)) = 1
    rw [det_unip, map_one]
  have hct : F₀ = fun g => PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 g * ((chiDet N χ g : ℂˣ) : ℂ) := by
    rw [hF₀]
    funext g
    simp only [PositivityTheory.Affgl.CT.ct]
    rw [← integral_mul_const]
    congr 1
    funext x
    rw [mulChi_apply, map_mul, hu, one_mul]
  have hYX : ∀ g, ((chiDet N χ g : ℂˣ) : ℂ) * Y g = 1 := fun g => Units.mul_inv _
  have hYa : ∀ t : ℝ, Y (aT E N r t) = Complex.exp (-(z * r * (Module.finrank ℚ E : ℂ) * t)) := fun t => by
    simp only [hY]
    rw [Units.val_inv_eq_inv_val, ExponentTwist.chiDet_aT hrN.le, ← Complex.exp_neg]
  refine ⟨PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1, ⟨μ, 𝓕, hμ, h𝓕, rfl⟩, LinearMap.mulRight ℂ Y F, ?_, ?_, ?_⟩
  · have h1 := Submodule.mem_map_of_mem (f := LinearMap.mulRight ℂ Y) hF
    rw [Submodule.map_span] at h1
    refine Submodule.span_le.2 ?_ h1
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    have e : LinearMap.mulRight ℂ Y (fun g => F₀ (aT E N r t * g)) =
        ((chiDet N χ (aT E N r t) : ℂˣ) : ℂ) • fun g => PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 (aT E N r t * g) := by
      funext g
      simp only [LinearMap.mulRight_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, hct, map_mul, Units.val_mul]
      linear_combination (PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 (aT E N r t * g) * ((chiDet N χ (aT E N r t) : ℂˣ) : ℂ)) * hYX g
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  · intro h
    apply hF0
    funext g
    have h2 := congrFun h g
    simp only [LinearMap.mulRight_apply, Pi.mul_apply, Pi.zero_apply] at h2
    have h3 : Y g ≠ 0 := Units.ne_zero _
    exact (mul_eq_zero.1 h2).resolve_right h3
  · intro t g
    simp only [LinearMap.mulRight_apply, Pi.mul_apply]
    have hYm : ∀ a b, Y (a * b) = Y a * Y b := fun a b => by simp only [hY, map_mul, mul_inv, Units.val_mul]
    have e : Complex.exp ((c - z * r * (Module.finrank ℚ E : ℂ)) * t) =
        Complex.exp (c * t) * Complex.exp (-(z * r * (Module.finrank ℚ E : ℂ) * t)) := by
      rw [← Complex.exp_add]; ring_nf
    rw [hFt, hYm, hYa, e]
    ring

end PositivityTheory.Rg.Rs
end
end
