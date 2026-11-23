module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatGlueLatIffDual
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneTmulSmulEqAddOfAlgebraMapEqAdd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle169
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSignatureFromBlocks
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle029
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle281
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle284
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle270
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle161
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle139
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Matrix.ColumnRowPartitioned
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
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle223

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom

namespace GlobalTheory.GluedCmp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Algebra

variable {A : Type} [CommRing A] {n k : ℕ} (m : Matrix (Fin n) (Fin k) A) (z : Fin n → A) {e t T : A}

theorem unit_fwd (he : e * e = e) (ht : t * T = 1) (x f : Fin k → A) (a : A) :
    e • (m *ᵥ (x + a • f) + (a * t) • z) = m *ᵥ (e • x + (a * (e * t)) • T • f) + (a * (e * t) * e) • z ∧
      e • (e • x + (a * (e * t)) • T • f) = e • x + (a * (e * t)) • T • f := by
  have h1 : a * (e * t) * e = e * (a * t) := by linear_combination (a * t) * he
  have h2 : a * (e * t) * T = e * a := by linear_combination (a * e) * ht
  rw [h1, smul_smul (a * (e * t)) T f, h2]
  refine ⟨?_, ?_⟩
  · simp only [Matrix.mulVec_add, Matrix.mulVec_smul, smul_add, smul_smul]
  · simp only [smul_add, smul_smul, ← mul_assoc, he]

theorem unit_bwd (he : e * e = e) (ht : t * T = 1) (x f : Fin k → A) (hx : e • x = x) (a : A) :
    m *ᵥ x + (a * e) • z = m *ᵥ ((x - (a * e) • T • f) + (a * e * T) • f) + (a * e * T * t) • z ∧
      e • (m *ᵥ x + (a * e) • z) = m *ᵥ x + (a * e) • z := by
  have h1 : a * e * T * t = a * e := by linear_combination (a * e) * ht
  have h2 : e * (a * e) = a * e := by linear_combination a * he
  refine ⟨?_, ?_⟩
  · rw [h1, smul_smul (a * e) T f, sub_add_cancel]
  · rw [smul_add, ← Matrix.mulVec_smul, hx, smul_smul, h2]

theorem glue_fwd (he : e * e = e) (x f g : Fin k → A) (hg : e • g = g) (a : A) :
    e • (m *ᵥ (x + a • f) + (a * t) • z) = m *ᵥ (e • x - a • (g - e • f)) + a • ((t * e) • z + m *ᵥ g) ∧
      e • (e • x - a • (g - e • f)) = e • x - a • (g - e • f) := by
  have hs : e • (g - e • f) = g - e • f := by rw [smul_sub, hg, smul_smul, he]
  refine ⟨?_, ?_⟩
  · simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, smul_add, smul_sub, smul_smul]
    module
  · rw [smul_sub e (e • x) (a • (g - e • f)), smul_smul e e x, he, smul_comm e a (g - e • f), hs]

theorem glue_bwd (he : e * e = e) (x f g : Fin k → A) (hx : e • x = x) (hg : e • g = g) (a : A) :
    m *ᵥ x + a • ((t * e) • z + m *ᵥ g) = m *ᵥ ((x + a • (g - e • f)) + (a * e) • f) + (a * e * t) • z ∧
      e • (m *ᵥ x + a • ((t * e) • z + m *ᵥ g)) = m *ᵥ x + a • ((t * e) • z + m *ᵥ g) := by
  have h2 : e * (t * e) = t * e := by linear_combination t * he
  refine ⟨?_, ?_⟩
  · simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, smul_add, smul_sub, smul_smul]
    module
  · rw [smul_add e (m *ᵥ x), ← Matrix.mulVec_smul m e x, hx, smul_comm e a, smul_add e ((t * e) • z),
      smul_smul e (t * e) z, h2, ← Matrix.mulVec_smul m e g, hg]

theorem idem_smul_smul (he : e * e = e) (y : Fin n → A) : e • e • y = e • y := by
  rw [smul_smul, he]

end Algebra

variable {D : D7} {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {z : Y.V} {u : D.what₂.Word} {L₀ : Lat X} {x₀ : X.V}

theorem fg_glueLat (h : L₀.FG) : (glueLat Y X ι z u L₀ x₀).FG := by
  unfold glueLat
  refine Submodule.FG.sup ?_ (Submodule.fg_span_singleton _)
  refine Submodule.FG.map _ ?_
  rw [show (Formalism.L2.Herm.crd X).toLinearMap.restrictScalars (𝓞 D.host.E) =
      (((Formalism.L2.Herm.crd X).restrictScalars (𝓞 D.host.E) : X.V ≃ₗ[𝓞 D.host.E] _) : X.V →ₗ[𝓞 D.host.E] _) from rfl,
    Submodule.comap_equiv_eq_map_symm]
  exact h.map _

theorem cmp_unit (hg : IsGlueVec X u L₀ (vA X x₀)) {w : Pl D.host.E}
    (hw : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) (y : Fin Y.rank → EAf D) :
    InCmp (idem w) (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) y ↔
      ∃ x, InCmp (idem w) L₀ x ∧ ∃ a ∈ OA D, y = mA Y X ι *ᵥ x + (a * idem w) • vA Y z := by
  have he := idem_mul_self w
  have ht := inc_inv_mul u
  have het : idem w * inc D (Tu D u)⁻¹ ∈ OA D := (idem_mul_inv_mem_iff u w).2 hw
  have hew := idem_mem w
  unfold InCmp
  constructor
  · rintro ⟨hy, hey⟩
    obtain ⟨x, hx, a, ha, rfl⟩ := (mem_hat_glueLat y).1 hy
    obtain ⟨h1, h2⟩ := unit_fwd (mA Y X ι) (vA Y z) he ht x (vA X x₀) a
    refine ⟨idem w • x + (a * (idem w * inc D (Tu D u)⁻¹)) • inc D (Tu D u) • vA X x₀,
      ⟨add_mem_hat (smul_mem_hat hew hx) (smul_mem_hat (mul_mem ha het) hg.mul_mem), h2⟩,
      a * (idem w * inc D (Tu D u)⁻¹), mul_mem ha het, ?_⟩
    rw [← hey, h1]
  · rintro ⟨x, ⟨hx, hex⟩, a, ha, rfl⟩
    obtain ⟨h1, h2⟩ := unit_bwd (mA Y X ι) (vA Y z) he ht x (vA X x₀) hex a
    refine ⟨?_, h2⟩
    rw [h1]
    exact (mem_hat_glueLat _).2 ⟨_, sub_mem_hat hx (smul_mem_hat (mul_mem ha hew) hg.mul_mem), _,
      mul_mem (mul_mem ha hew) (inc_Tu_mem u), rfl⟩

theorem cmp_glue {w : Pl D.host.E} {g : Fin X.rank → EAf D} (h1 : idem w • g = g)
    (h2 : g - idem w • vA X x₀ ∈ hat L₀) (y : Fin Y.rank → EAf D) :
    InCmp (idem w) (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) y ↔
      ∃ x, InCmp (idem w) L₀ x ∧ ∃ a ∈ OA D,
        y = mA Y X ι *ᵥ x + a • ((inc D (Tu D u)⁻¹ * idem w) • vA Y z + mA Y X ι *ᵥ g) := by
  have he := idem_mul_self w
  have hew := idem_mem w
  unfold InCmp
  constructor
  · rintro ⟨hy, hey⟩
    obtain ⟨x, hx, a, ha, rfl⟩ := (mem_hat_glueLat y).1 hy
    obtain ⟨k1, k2⟩ := glue_fwd (mA Y X ι) (vA Y z) (t := inc D (Tu D u)⁻¹) he x (vA X x₀) g h1 a
    refine ⟨idem w • x - a • (g - idem w • vA X x₀),
      ⟨sub_mem_hat (smul_mem_hat hew hx) (smul_mem_hat ha h2), k2⟩, a, ha, ?_⟩
    rw [← hey, k1]
  · rintro ⟨x, ⟨hx, hex⟩, a, ha, rfl⟩
    obtain ⟨k1, k2⟩ := glue_bwd (mA Y X ι) (vA Y z) (t := inc D (Tu D u)⁻¹) he x (vA X x₀) g hex h1 a
    refine ⟨?_, k2⟩
    rw [k1]
    exact (mem_hat_glueLat _).2 ⟨_, add_mem_hat hx (smul_mem_hat ha h2), _, mul_mem ha hew, rfl⟩

theorem cmp_conj (h : IsLine Y X ι z u) (hg : IsGlueVec X u L₀ (vA X x₀)) (w : Pl D.host.E) (y : Fin Y.rank → EAf D) :
    InCmp (cjA D (idem w)) (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) y ↔
      cjA D (idem w) • y = y ∧ (∃ (x : Fin X.rank → EAf D) (a : EAf D), y = mA Y X ι *ᵥ x + a • vA Y z) ∧
        ∀ y', InCmp (idem w) (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) y' → hA Y y' y ∈ OA D := by
  have hew := idem_mem w
  unfold InCmp
  constructor
  · rintro ⟨hy, hcy⟩
    obtain ⟨x, hx, a, ha, rfl⟩ := (mem_hat_glueLat y).1 hy
    refine ⟨hcy, ⟨x + a • vA X x₀, a * inc D (Tu D u)⁻¹, rfl⟩, ?_⟩
    rintro y' ⟨hy', -⟩
    exact (mem_hat_glueLat_iff_dual h hg _ _).1 hy y' hy'
  · rintro ⟨hcy, ⟨x, a, rfl⟩, hdual⟩
    refine ⟨(mem_hat_glueLat_iff_dual h hg x a).2 ?_, hcy⟩
    intro y'' hy''
    have key : hA Y y'' (mA Y X ι *ᵥ x + a • vA Y z) =
        hA Y (idem w • y'') (mA Y X ι *ᵥ x + a • vA Y z) := by
      conv_lhs => rw [← hcy]
      rw [hA_smul_right, hA_smul_left, cjA_cjA]
    rw [key]
    exact hdual _ ⟨smul_mem_hat hew hy'', idem_smul_smul (idem_mul_self w) y''⟩

theorem isGlued_glueLat : ∀ (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V)
    (z : Y.V), IsLine Y X ι z u → ∀ (L₀ : Lat X) (x₀ : X.V) (f₀ : Pl D.host.E → Fin X.rank → EAf D),
    Submodule.IsLattice D.host.E L₀ → IsGlueVec X u L₀ (vA X x₀) →
    (∀ w : Pl D.host.E, π ∈ w.asIdeal → idem w • f₀ w = f₀ w ∧ f₀ w - idem w • vA X x₀ ∈ hat L₀) →
    IsGlued Y X ι z u π L₀ f₀ (glueLat Y X ι z u L₀ x₀) := by
  intro D u π Y X ι z h L₀ x₀ f₀ hL hg hf
  unfold IsGlued
  refine ⟨fg_glueLat hL.fg, ?_, ?_⟩
  · intro w e he hw y
    obtain rfl := eq_idem he
    exact cmp_unit hg hw y
  · intro w e he hπ
    obtain rfl := eq_idem he
    exact ⟨fun y => cmp_glue (hf w hπ).1 (hf w hπ).2 y, cmp_conj h hg w⟩

end GlobalTheory.GluedCmp

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StandardGramVectors

open GlobalTheory.FrameComplement GlobalTheory.DetNorm

def stdGram (K : Type) [Field K] (ρ ε : ℕ) (t : K) :
    Matrix ((Fin ρ ⊕ Fin ρ) ⊕ Fin ε) ((Fin ρ ⊕ Fin ρ) ⊕ Fin ε) K :=
  fromBlocks (fromBlocks 0 1 1 0) 0 0 ((-t) • 1)

theorem hasSignature_submatrix {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {J : Matrix n n ℂ} {p q : ℕ} (h : Formalism.UG.HasSignature J p q) (e : m ≃ n) :
    Formalism.UG.HasSignature (J.submatrix e e) p q := by
  obtain ⟨c, Q, hQ⟩ := Formalism.UG.P.sig_data _ _ _ h
  refine hasSignature_of_frame (by rw [Fintype.card_congr e, c]) (Q.submatrix e id) ?_
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_id_id, hQ]

theorem hasSignature_stdGram (ρ ε : ℕ) {T : ℕ} (hT : 0 < T) :
    Formalism.UG.HasSignature (stdGram ℂ ρ ε (T : ℂ)) (ρ + 0) (ρ + ε) := by
  refine hasSignature_fromBlocks ?_ ?_
  · refine hasSignature_of_frame (by simp) (fromBlocks 1 1 ((1 / 2 : ℂ) • 1) ((-1 / 2 : ℂ) • 1)) ?_
    simp only [fromBlocks_conjTranspose, fromBlocks_multiply, Formalism.UG.Jpq, conjTranspose_smul, conjTranspose_one]
    ext (r | r) (s | s) <;> by_cases h : r = s <;> simp [h] <;> norm_num
  · have h1 : ((√(T : ℝ) : ℝ) : ℂ) * ((√(T : ℝ) : ℝ) : ℂ) = T := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg T)]; simp
    have h2 : ((√(T : ℝ) : ℝ) : ℂ) ≠ 0 := fun h => by
      rw [h, mul_zero] at h1
      exact hT.ne' (by exact_mod_cast h1.symm)
    refine hasSignature_of_frame (by simp) (fromCols 0 ((((√(T : ℝ) : ℝ) : ℂ))⁻¹ • 1)) ?_
    ext (r | r) (s | s)
    · exact r.elim0
    · exact r.elim0
    · exact s.elim0
    · rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, fromRows_mul_fromCols]
      by_cases h : r = s
      · simp [h, Formalism.UG.Jpq]
        rw [← h1]; field_simp
      · simp [h, Formalism.UG.Jpq]

theorem det_stdGram (K : Type) [Field K] (ρ ε : ℕ) (t : K) :
    ∃ s : K, s * s = 1 ∧ (stdGram K ρ ε t).det = s * (-t) ^ ε := by
  refine ⟨(fromBlocks 0 1 1 0 : Matrix (Fin ρ ⊕ Fin ρ) (Fin ρ ⊕ Fin ρ) K).det, ?_, ?_⟩
  · rw [← Matrix.det_mul, Matrix.fromBlocks_multiply]
    simp
  · rw [stdGram, det_fromBlocks_zero₂₁, det_smul, det_one, mul_one, Fintype.card_fin]

theorem gram_comb {E : Type} [Field E] [NumberField E] [StarRing E] (Y : HSpace E) {c : ℕ} (b : Fin c → Y.V)
    (P : Matrix (Fin c) (Fin c) E) (k l : Fin c) :
    Y.hT (∑ i, P i k • b i) (∑ i, P i l • b i) = (Pᴴ * (Matrix.of fun i l => Y.hT (b i) (b l)) * P) k l := by

  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, map_smul,
  LinearMap.map_smulₛₗ₂, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
  starRingEnd_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem isN_pow {D : D7} {x : D.host.E} (h : IsN D x) (n : ℕ) : IsN D (x ^ n) := by
  induction n with
  | zero => simpa using isN_star (D := D) 1
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem exists_std (D : D7) (j : ℕ) (hj : j < D.R.m) :
    ∃ w : (Fin ((D.R.m - 1 - j) / 2) ⊕ Fin ((D.R.m - 1 - j) / 2)) ⊕ Fin ((D.R.m - 1 - j) % 2) → (D.sp.Y j).V,
      (∀ k x, (D.sp.Y j).hT (D.sp.iXY j x) (w k) = 0) ∧
      ∀ k l, (D.sp.Y j).hT (w k) (w l) = stdGram D.host.E _ _ (D.sp.T : D.host.E) k l := by
  obtain ⟨b, hb, hd, hs, a, ha, hdet⟩ := exists_complement_XY D j hj
  generalize D.R.m - 1 - j = c at *
  have hT : 0 < D.sp.T := D.sp.T_prime.pos
  obtain ⟨e⟩ : Nonempty (Fin c ≃ (Fin (c / 2) ⊕ Fin (c / 2)) ⊕ Fin (c % 2)) :=
    Fintype.card_eq.1 (by simp; omega)
  obtain ⟨s, hs1, hs2⟩ := det_stdGram D.host.E (c / 2) (c % 2) (D.sp.T : D.host.E)
  have hsN : IsN D s ∧ star s = s := by
    rcases mul_self_eq_one_iff.1 hs1 with h | h
    · rw [h]; exact ⟨by simpa using isN_star (D := D) 1, star_one _⟩
    · rw [h]; exact ⟨isN_neg_one, by simp⟩
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs1
  have hT0 : (D.sp.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hT.ne'
  have hX := GlobalTheory.FrameComplement.gram_det_ne (D.sp.X j)
  obtain ⟨P, -, hP⟩ := GlobalTheory.HermAdelicNorm.congr_of_signature_of_adelic_norm D.host.F D.host.E D.sp.cm c
    (Matrix.of fun i l => (D.sp.Y j).hT (b i) (b l))
    ((stdGram D.host.E (c / 2) (c % 2) (D.sp.T : D.host.E)).submatrix e e)
    (Matrix.ext fun i l => (D.sp.Y j).herm.eq _ _)
    (by simp [stdGram, conjTranspose_submatrix, fromBlocks_conjTranspose]) hd
    (by rw [det_submatrix_equiv_self, hs2]; exact mul_ne_zero hs0 (pow_ne_zero _ (neg_ne_zero.2 hT0)))
    (fun τ => ⟨_, _, hs τ, by
      have h1 : ((stdGram D.host.E (c / 2) (c % 2) (D.sp.T : D.host.E)).submatrix e e).map τ =
          (stdGram ℂ (c / 2) (c % 2) (D.sp.T : ℂ)).submatrix e e := by
        ext r t
        simp only [map_apply, submatrix_apply]
        rcases e r with (r | r) | r <;> rcases e t with (t | t) | t <;>
          simp [stdGram, Matrix.one_apply, apply_ite τ]
      rw [h1]
      convert hasSignature_submatrix (hasSignature_stdGram (c / 2) (c % 2) hT) e using 1 <;> omega⟩)
    (by
      have h1 : IsN D (-(D.sp.T : D.host.E)) := by simpa using (isN_neg_one (D := D)).mul isNormFromTensorFiniteAdele_levelNormT
      have h2 := (((isN_det (D.sp.Y j)).mul ((isN_det (D.sp.X j)).inv (star_det _))).mul (isN_star a⁻¹)).mul
        ((hsN.1.mul (isN_pow h1 (c % 2))).inv (by simp [hsN.2]))
      have ha' : star a ≠ 0 := star_ne_zero.2 ha
      have h3 : ∀ x g u : D.host.E, x ≠ 0 → star a * a * x * g * x⁻¹ * (star a⁻¹ * a⁻¹) * u⁻¹ = g / u :=
        fun x g u hx => by rw [star_inv₀, div_eq_mul_inv]; field_simp
      rw [hdet, h3 _ _ _ hX] at h2
      rw [det_submatrix_equiv_self, hs2]
      exact h2)
  refine ⟨fun k => ∑ i, P i (e.symm k) • b i, fun k x => ?_, fun k l => ?_⟩
  · simp [hb]
  · rw [gram_comb, hP, submatrix_apply, e.apply_symm_apply, e.apply_symm_apply]

theorem exists_auxiliaryHyperbolicVectors : ∀ (D : D7) (j : ℕ), j < D.R.m → ∃ (E Ev : ℕ → (D.sp.Y j).V) (z : (D.sp.Y j).V), GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.IsAuxiliaryHeckeCharacter D j E Ev z := by
  intro D j hj
  obtain ⟨w, h0, hw⟩ := exists_std D j hj
  refine ⟨fun i => if h : i < (D.R.m - 1 - j) / 2 then w (.inl (.inl ⟨i, h⟩)) else 0,
    fun i => if h : i < (D.R.m - 1 - j) / 2 then w (.inl (.inr ⟨i, h⟩)) else 0,
    if h : 0 < (D.R.m - 1 - j) % 2 then w (.inr ⟨0, h⟩) else 0, ?_⟩
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.IsAuxiliaryHeckeCharacter GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.nAux HSpace.hD
  refine ⟨fun i hi l hl => ?_, fun i hi x => ?_, fun he => ?_⟩
  · simp only [dif_pos hi, dif_pos hl, hw]
    simp [stdGram, Matrix.one_apply, Fin.ext_iff, eq_comm]
  · simp only [dif_pos hi, h0, and_self]
  · have h : 0 < (D.R.m - 1 - j) % 2 := by
      obtain ⟨a, ha⟩ := D.R.m_even
      obtain ⟨b, hb⟩ := he
      omega
    refine ⟨?_, fun x => ?_, fun i hi => ?_⟩
    · simp only [dif_pos h, hw]; simp [stdGram]
    · simp only [dif_pos h, h0]
    · simp only [dif_pos h, dif_pos hi, hw]; simp [stdGram]

end GlobalTheory.StandardGramVectors
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

noncomputable section
namespace GlobalTheory.SeeConjGroup

theorem fmat_iota_eq_finE : ∀ {D : D7} (κ : GA D (Yc D 0)), (GlobalTheory.SeeConjGroup.II D).fmat ((Formalism.IndefR.RationalEmbedding.iota D) κ).2 = (finE (Yc D 0) κ).val := by
  intro D κ
  have e : (Formalism.IndefR.RationalEmbedding.iota D).symm (Formalism.IndefR.RationalEmbedding.iota D κ) = κ := (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply κ
  have hf := Formalism.L2.SG.EvalTIota.finE_brg_i (Formalism.IndefR.RationalEmbedding.iota D κ)
  rw [e] at hf
  have hv := congrArg Units.val hf
  exact hv.symm ▸ rfl
end GlobalTheory.SeeConjGroup
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_selfDual_frame_of_standard_selfDual_lattice : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), (Λ : Set (Fin V.rank → D.host.E)) = L0c D V → IsSelfDualC V Λ → ∃ β, IsSDFrame V β Λ 1 := by
  first | exact @GlobalTheory.SDFrameCompletion.exists_isSDFrame_of_isSelfDualC | exact GlobalTheory.SDFrameCompletion.exists_isSDFrame_of_isSelfDualC | (intros; apply GlobalTheory.SDFrameCompletion.exists_isSDFrame_of_isSelfDualC <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem finiteGroup_acts_unitarily_hilbertMultiplicityModel : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S), ∀ (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) J χ, ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e : H →ₗ[ℂ] MMap M) (d : ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), (∀ x y, inner ℂ x y = d * ipM M μ 𝓕 (e x) (e y)) → Function.Injective e → (∀ x, e x ∈ Mult θ M J χ) → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → ∀ (g0 : G0 L.Pg L.r) (u : H ≃ₗ[ℂ] H), (∀ x v, e (u x) v = actG0 V β L g0 (e x v)) → ∀ x, ‖u x‖ = ‖x‖ := by
  intro D V S θ M β L J χ H _ _ e d μ 𝓕 hin hinj hmem hμ h𝓕 g0 u hact x
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hμ

  have hchoose : ∀ (P Q : ℂ → Prop) (hP : ∃ c, P c) (hQ : ∃ c, Q c), P = Q → hP.choose = hQ.choose := by
    rintro P Q hP hQ rfl; rfl
  have hip : ipM M μ 𝓕 (e (u x)) (e (u x)) = ipM M μ 𝓕 (e x) (e x) := by
    by_cases hk : ∃ κ, IsLevelLift V β L g0 κ
    · obtain ⟨hcpt, hlift⟩ := GlobalTheory.T.isCompact_parahoricLevel_and_contains_lifts V β L
      have hκ : hk.choose ∈ levG V β (flagL L) := hlift g0 _ hk.choose_spec
      have hκi : hk.choose⁻¹ ∈ levG V β (flagL L) := inv_mem hκ
      set a : ℂ := (levChi V β (flagL L) hk.choose)⁻¹ with ha_def
      have ha : ‖a‖ = 1 := by rw [ha_def, norm_inv, GlobalTheory.norm_levChi_flagL_eq_one V β L _ hκ, inv_one]
      have ha0 : a ≠ 0 := by intro h; rw [h, norm_zero] at ha; exact zero_ne_one ha
      have hai : ‖a⁻¹‖ = 1 := by rw [norm_inv, ha, inv_one]
      have hU : ∀ v g, e (u x) v g = a * e x v (g * hk.choose) := by
        intro v g
        rw [hact x v]
        simp only [actG0, dif_pos hk, ha_def]
      have hV : ∀ v g, e x v g = a⁻¹ * e (u x) v (g * hk.choose⁻¹) := by
        intro v g
        rw [hU, mul_assoc g, inv_mul_cancel, mul_one, ← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
      have hm1 := GlobalTheory.haar_map_mul_right_of_mem_compact_subgroup μ _ hcpt _ hκ
      have hm2 := GlobalTheory.haar_map_mul_right_of_mem_compact_subgroup μ _ hcpt _ hκi
      have hiff : ∀ c, IsMultIP M μ 𝓕 (e (u x)) (e (u x)) c ↔ IsMultIP M μ 𝓕 (e x) (e x) c := by
        intro c
        constructor
        · intro hc
          exact GlobalTheory.T.multiplicityInnerProduct_unit_twisted_right_translation θ M J χ μ 𝓕 hμ h𝓕 _ _ hai hm2 _ (hmem (u x)) _ (hmem (u x)) _ _ hV hV c hc
        · intro hc
          exact GlobalTheory.T.multiplicityInnerProduct_unit_twisted_right_translation θ M J χ μ 𝓕 hμ h𝓕 _ _ ha hm1 _ (hmem x) _ (hmem x) _ _ hU hU c hc
      unfold ipM
      split_ifs with h1 h2 h2
      · exact hchoose _ _ h1 h2 (funext fun c => propext (hiff c))
      · exact absurd (let ⟨c, hc⟩ := h1; ⟨c, (hiff c).1 hc⟩) h2
      · exact absurd (let ⟨c, hc⟩ := h2; ⟨c, (hiff c).2 hc⟩) h1
      · rfl
    ·
      have h0 : e (u x) = 0 := by
        ext v g
        rw [hact x v]
        simp only [actG0, dif_neg hk]
        rfl
      have hux : u x = 0 := hinj (by rw [h0, map_zero])
      have hx : x = 0 := by
        have := congrArg u.symm hux
        simpa using this
      rw [hux, hx]
  have hsq' : ‖u x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), hin, hin, hip]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq'

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_unitary_matching_frames_at_nonconjugate_places : ∀ {D : D7} (V : HSp D) (Pg : Finset (Pl D.host.E)), (∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl (D := D) PP PP') → ∀ β₁ β₂ : GL (Fin V.rank) (EAf D), IsFrame β₁ (Formalism.L2.Herm.crdLat V V.L0) → IsFrame β₂ (Formalism.L2.Herm.crdLat V V.L0) → ∃ u ∈ GfC V, IsFrame (finE V u * β₁) (Formalism.L2.Herm.crdLat V V.L0) ∧ ∀ PP ∈ Pg, ∀ x, redFn (finE V u * β₁) PP x = redFn β₂ PP x := by
  first | exact @GlobalTheory.FrameMatch.frames_match | exact GlobalTheory.FrameMatch.frames_match | (intros; apply GlobalTheory.FrameMatch.frames_match <;> assumption)
end
