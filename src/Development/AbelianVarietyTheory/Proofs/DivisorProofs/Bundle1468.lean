module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1372
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

@[expose] public section

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

noncomputable section

namespace GlobalTheory.CentralExponent

open Matrix GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele GlobalTheory.IdeleCovolume GlobalTheory.UnitaryBC

theorem abs_le_of_conj_mem : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a →
    ∀ W : Set (GA E a), IsCompact W → ∃ n₀ : ℕ, ∀ (γ : GL (Fin a) E) (n : ℤ) (g : GA E a),
      g⁻¹ * (ratGL E a γ * GlobalTheory.UnitaryBC.splitCentre E a 1 ^ n) * g ∈ W → |n| ≤ n₀ := by
  intro E _ _ _ a ha W hW
  have hL : 0 < Real.log (ideleNorm (E := E) (eIdele E)) := Real.log_pos (one_lt_ideleNorm_eIdele E)
  have hc : Continuous fun x : GA E a => Real.log (ideleNorm (E := E) (GeneralLinearGroup.det x)) :=
    (continuous_ideleNorm.comp GeneralLinearGroup.continuous_det).log fun _ => ideleNorm_ne_zero _
  obtain ⟨C, hC⟩ := hW.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨⌈C / Real.log (ideleNorm (E := E) (eIdele E))⌉₊, fun γ n g hmem => ?_⟩
  have hd : GeneralLinearGroup.det (ratGL E a γ) = diag E (GeneralLinearGroup.det γ) :=
    Units.ext (by rw [ratGL, GlobalTheory.CuspRep.det_map]; rfl)
  have e : GeneralLinearGroup.det (g⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * g) =
      diag E (GeneralLinearGroup.det γ) * eIdele E ^ ((a : ℤ) * n) := by
    rw [map_mul, map_mul, map_mul, map_inv, map_zpow, hd, det_splitCentre_one, ← zpow_natCast, ← _root_.zpow_mul,
      mul_comm _ (GeneralLinearGroup.det g), mul_inv_cancel_left]
  have key : Real.log (ideleNorm (E := E) (GeneralLinearGroup.det
      (g⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * g))) =
      ((a : ℤ) * n : ℤ) * Real.log (ideleNorm (E := E) (eIdele E)) := by
    rw [e, map_mul, show ideleNorm (E := E) (diag E _) = 1 from ideleNorm_principalIdele _, one_mul, map_zpow,
      Real.log_zpow]
  have h1 := hC _ hmem
  rw [key, Real.norm_eq_abs, abs_mul, abs_of_pos hL] at h1
  have h2 : (|n| : ℝ) ≤ |(((a : ℤ) * n : ℤ) : ℝ)| := by
    push_cast
    rw [abs_mul, Nat.abs_cast]
    exact le_mul_of_one_le_left (abs_nonneg _) (by exact_mod_cast ha)
  have h3 : (|n| : ℝ) ≤ ⌈C / Real.log (ideleNorm (E := E) (eIdele E))⌉₊ :=
    (h2.trans ((le_div_iff₀ hL).2 h1)).trans (Nat.le_ceil _)
  exact_mod_cast h3

end GlobalTheory.CentralExponent
end
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

noncomputable section

namespace GlobalTheory.CuspRep.SplitDeriv

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem hasDerivAt_scalar_exp :
    HasDerivAt (fun t : ℝ =>
      toL (Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => (t : ℂ))).val)
      (fun i j => if i = j then (1 : Cinf E) else 0) 0 := by
  rw [hasDerivAt_pi]; intro i
  rw [hasDerivAt_pi]; intro j
  rw [hasDerivAt_pi]; intro w
  by_cases h : i = j
  · subst h
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
    have h2 := h1.cexp
    simpa [toL, Matrix.scalar_apply, Matrix.diagonal_apply, expU] using h2
  · simpa [toL, Matrix.scalar_apply, Matrix.diagonal_apply, h] using hasDerivAt_const (0 : ℝ) (0 : ℂ)


open GlobalTheory.UnitaryBC in
theorem hasDerivAt_splitCentre (ψ : Sm E a) (g : GA E a) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ψ.1 (g * splitCentre E a t))
      ((lie E a (fun i j => if i = j then (1 : Cinf E) else 0) ψ).1 (g * splitCentre E a s)) s := by
  have h0 : Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => ((0 : ℝ) : ℂ)) = 1 := by
    ext i j w
    by_cases h : i = j <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply, expU, Matrix.one_apply, h]
  have h := hasDerivAt_curve ψ (g * splitCentre E a s)
    (fun t => Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => (t : ℂ)))
    _ h0 hasDerivAt_scalar_exp
  have h' := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact h)
  rw [lie_apply]
  refine h'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  change ψ.1 (g * splitCentre E a t) = ψ.1 (g * splitCentre E a s * splitCentre E a (t - s))
  rw [mul_assoc, ← splitCentre_add, add_sub_cancel]

end GlobalTheory.CuspRep.SplitDeriv
end
end

section

noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SiegelCells

variable {D : D7} {n : ℕ}

def lastDiag (R : Type) [Zero R] [One R] (n j : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.diagonal fun i => if n - j ≤ i.val then 1 else 0

def wMat (R : Type) [Ring R] (n j : ℕ) : Matrix (Fin (n + n)) (Fin (n + n)) R :=
  StdUnn.blk4 (1 - lastDiag R n j) (lastDiag R n j) (-lastDiag R n j) (1 - lastDiag R n j)

theorem lastDiag_mul_self (R : Type) [Ring R] (n j : ℕ) : lastDiag R n j * lastDiag R n j = lastDiag R n j := by
  simp only [lastDiag, Matrix.diagonal_mul_diagonal]
  congr 1; funext i; split_ifs <;> simp

theorem lastDiag_mul_one_sub (R : Type) [Ring R] (n j : ℕ) : lastDiag R n j * (1 - lastDiag R n j) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, lastDiag_mul_self, sub_self]

theorem one_sub_mul_lastDiag (R : Type) [Ring R] (n j : ℕ) : (1 - lastDiag R n j) * lastDiag R n j = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, lastDiag_mul_self, sub_self]

theorem adj_lastDiag {j : ℕ} : adj (lastDiag (AE D) n j) = lastDiag (AE D) n j := by
  ext i k
  simp only [adj, lastDiag, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply]
  by_cases h : k = i
  · subst h; split_ifs <;> simp
  · simp [h, Ne.symm h]

theorem wMat_key {R : Type} [CommRing R] {n : ℕ} (L : Matrix (Fin n) (Fin n) R) (h : L * L = L) :
    StdUnn.blk4 (1 - L) (-L) L (1 - L) * StdUnn.blk4 0 1 (-1) 0 * StdUnn.blk4 (1 - L) L (-L) (1 - L) =
      StdUnn.blk4 0 1 (-1) 0 := by
  rw [StdUnn.Model.submatrix_fromBlocks_mul, StdUnn.Model.submatrix_fromBlocks_mul]
  have h1 : (1 - L) * (1 - L) = 1 - L := by rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, h, sub_self, sub_zero]
  have h2 : L * (1 - L) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, h, sub_self]
  have h3 : (1 - L) * L = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, h, sub_self]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul, neg_neg,
    add_zero, zero_add]
  congr 1
  · simp only [Matrix.add_mul, Matrix.neg_mul, Matrix.mul_neg, h2, h3, neg_zero, add_zero]
  · simp only [Matrix.add_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg, h, h1, h2, h3]; abel
  · rw [h1, h]; abel
  · rw [h2, h3]; simp

theorem exists_wPart (j : ℕ) : ∃ g : StdUnn.G D n, StdUnn.mat g = wMat (AE D) n j := by
  have e1 := lastDiag_mul_self (AE D) n j
  have e2 := lastDiag_mul_one_sub (AE D) n j
  have e3 := one_sub_mul_lastDiag (AE D) n j
  have e4 : (1 - lastDiag (AE D) n j) * (1 - lastDiag (AE D) n j) = 1 - lastDiag (AE D) n j := by
    rw [Matrix.sub_mul, Matrix.one_mul, e2, sub_zero]
  refine StdUnn.Model.exists_mat _ (StdUnn.blk4 (1 - lastDiag (AE D) n j) (-lastDiag (AE D) n j) (lastDiag (AE D) n j)
    (1 - lastDiag (AE D) n j)) ?_ ?_ ?_
  · simp only [wMat, StdUnn.Model.submatrix_fromBlocks_mul, e1, e2, e3, e4, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    rw [← StdUnn.Model.block_matrix_one]; congr 1 <;> abel
  · simp only [wMat, StdUnn.Model.submatrix_fromBlocks_mul, e1, e2, e3, e4, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    rw [← StdUnn.Model.block_matrix_one]; congr 1 <;> abel
  · have ha : adj (wMat (AE D) n j) = StdUnn.blk4 (1 - lastDiag (AE D) n j) (-lastDiag (AE D) n j) (lastDiag (AE D) n j)
        (1 - lastDiag (AE D) n j) := by
      rw [wMat, StdUnn.Model.adelicConjTranspose_blockMatrixTwoByTwoFin, adj_sub, adj_one, adj_neg, adj_lastDiag]
    rw [ha]
    exact wMat_key _ e1






end GlobalTheory.SiegelCells

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.SUSuppSub

section Mat

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] (c : R)

theorem fix_mul {A B : Matrix n n R} (hA : c • (A - 1) = A - 1) (hB : c • (B - 1) = B - 1) :
    c • (A * B - 1) = A * B - 1 := by
  have e : A * B - 1 = (A - 1) * B + (B - 1) := by rw [Matrix.sub_mul, Matrix.one_mul]; abel
  rw [e, smul_add, ← Matrix.smul_mul, hA, hB]

theorem fix_inv {A A' : Matrix n n R} (h : A' * A = 1) (hA : c • (A - 1) = A - 1) :
    c • (A' - 1) = A' - 1 := by
  have e : A' - 1 = -(A' * (A - 1)) := by rw [Matrix.mul_sub, h, Matrix.mul_one]; abel
  rw [e, smul_neg, ← Matrix.mul_smul, hA]

theorem fix_conj {A K K' : Matrix n n R} (h : K * K' = 1) (hA : c • (A - 1) = A - 1) :
    c • (K * A * K' - 1) = K * A * K' - 1 := by
  have e : K * A * K' - 1 = K * (A - 1) * K' := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h]
  rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, hA]

end Mat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

abbrev mv (g : HA (AF F) σ J) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) :=
  ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))

theorem mv_mul (g h : HA (AF F) σ J) : mv σ J (g * h) = mv σ J g * mv σ J h := rfl

theorem mv_one : mv σ J 1 = 1 := rfl

theorem mv_inv_mul (g : HA (AF F) σ J) : mv σ J g⁻¹ * mv σ J g = 1 := by
  rw [← mv_mul, inv_mul_cancel, mv_one]

theorem mv_mul_inv (g : HA (AF F) σ J) : mv σ J g * mv σ J g⁻¹ = 1 := by
  rw [← mv_mul, mul_inv_cancel, mv_one]

theorem mem_SUSupp_iff {ε : AF F} {g : HA (AF F) σ J} : g ∈ SUSupp σ J ε ↔ g ∈ SUAdelic σ J ∧
    algebraMap (AF F) (AF F ⊗[F] E) ε • (mv σ J g - 1) = mv σ J g - 1 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    ext i j
    simpa using h2 i j
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i j => ?_⟩
    have := congrFun (congrFun h2 i) j
    simpa using this

theorem closure_div_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → ∀ x ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h}, ∀ y ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h}, x * y⁻¹ ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} := by
  intro F E _ _ _ _ _ σ _ M J _ S₁ S₂ ε _
  set c := algebraMap (AF F) (AF F ⊗[F] E) ε with hc
  set S := {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} with hS
  have hconj : ∀ k g : HA (AF F) σ J, g ∈ SUAdelic σ J → k * g * k⁻¹ ∈ SUAdelic σ J := by
    intro k g hg
    rw [StrongApprox.mem_SUAdelic] at hg ⊢
    change (mv σ J g).det = 1 at hg
    change (mv σ J (k * g * k⁻¹)).det = 1
    rw [mv_mul, mv_mul, Matrix.det_mul, Matrix.det_mul, hg, mul_one, ← Matrix.det_mul, mv_mul_inv,
      Matrix.det_one]
  have hdiv : ∀ x ∈ S, ∀ y ∈ S, x * y⁻¹ ∈ S := by
    rintro _ ⟨γ, hγ, h, hh, rfl⟩ _ ⟨γ', hγ', h', hh', rfl⟩
    refine ⟨γ * γ'⁻¹, (SURat σ J).mul_mem hγ ((SURat σ J).inv_mem hγ'), γ' * (h * h'⁻¹) * γ'⁻¹, ?_, by group⟩
    rw [mem_SUSupp_iff] at hh hh' ⊢
    refine ⟨hconj γ' _ ((SUAdelic σ J).mul_mem hh.1 ((SUAdelic σ J).inv_mem hh'.1)), ?_⟩
    rw [mv_mul, mv_mul, mv_mul]
    exact fix_conj _ (mv_mul_inv σ J γ') (fix_mul _ hh.2 (fix_inv _ (mv_inv_mul σ J h') hh'.2))
  have hne : S.Nonempty := ⟨1, 1, (SURat σ J).one_mem, 1,
    (mem_SUSupp_iff σ J).2 ⟨(SUAdelic σ J).one_mem, by rw [mv_one, sub_self, smul_zero]⟩, by simp⟩
  let P : Subgroup (HA (AF F) σ J) := Subgroup.ofDiv S hne hdiv
  have hP : (P.topologicalClosure : Set (HA (AF F) σ J)) = closure S := by
    rw [Subgroup.topologicalClosure_coe]; rfl
  intro x hx y hy
  rw [← hP] at hx hy ⊢
  exact P.topologicalClosure.mul_mem hx (P.topologicalClosure.inv_mem hy)

end GlobalTheory.SUSuppSub

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

noncomputable section
namespace GlobalTheory
open Classical

variable (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)

theorem ainf_single_mul (a b : w.Completion) :
    (show Ainf F from Pi.single w (a * b)) = (show Ainf F from Pi.single w a) * (show Ainf F from Pi.single w b) := by
  funext u
  change (Pi.single w (a*b) : ∀ v : InfinitePlace F, v.Completion) u =
    (Pi.single w a : ∀ v : InfinitePlace F, v.Completion) u * (Pi.single w b : ∀ v : InfinitePlace F, v.Completion) u
  by_cases h : u = w
  · subst h; simp only [Pi.single_eq_same]
  · simp only [Pi.single_eq_of_ne h, mul_zero]

theorem ainf_idem_mul (e : Ainf F) (h1 : e w = 1) (h0 : ∀ u, u ≠ w → e u = 0) (a : w.Completion) :
    e * (show Ainf F from Pi.single w a) = (show Ainf F from Pi.single w a) := by
  funext u
  change (e : ∀ v : InfinitePlace F, v.Completion) u * (Pi.single w a : ∀ v : InfinitePlace F, v.Completion) u = (Pi.single w a : ∀ v : InfinitePlace F, v.Completion) u
  by_cases h : u = w
  · subst h; rw [h1, one_mul]
  · simp only [Pi.single_eq_of_ne h, mul_zero]

theorem ainf_single_one (e : Ainf F) (h1 : e w = 1) (h0 : ∀ u, u ≠ w → e u = 0) :
    (show Ainf F from Pi.single w 1) = e := by
  funext u
  change (Pi.single w 1 : ∀ v : InfinitePlace F, v.Completion) u = e u
  by_cases h : u = w
  · subst h; rw [h1, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h, h0 u h]

theorem af_zero (y : Af F) (h : ∀ v, evalV F v y = 0) : y = 0 := by
  ext v
  exact congrArg _ (h v)

theorem af_ext {p q : AF F} (h1 : fstA F p = fstA F q) (h2 : sndA F p = sndA F q) : p = q :=
  Prod.ext h1 h2

def placeAtInf : w.Completion →ₗ[F] AF F :=
  (LinearMap.inl F (Ainf F) (Af F)).comp (LinearMap.single F (fun u : InfinitePlace F => u.Completion) w)

theorem fstA_placeAtInf (a : w.Completion) : fstA F (placeAtInf F w a) = (show Ainf F from Pi.single w a) := rfl
theorem sndA_placeAtInf (a : w.Completion) : sndA F (placeAtInf F w a) = 0 := rfl

theorem placeAtInf_mul (a b : w.Completion) :
    placeAtInf F w (a * b) = placeAtInf F w a * placeAtInf F w b := by
  apply af_ext
  · have e2 : fstA F (placeAtInf F w a * placeAtInf F w b) =
        fstA F (placeAtInf F w a) * fstA F (placeAtInf F w b) := map_mul (fstA F) _ _
    exact (fstA_placeAtInf F w (a * b)).trans ((ainf_single_mul F w a b).trans
      (e2.trans (congrArg₂ (· * ·) (fstA_placeAtInf F w a) (fstA_placeAtInf F w b))).symm)
  · have e2 : sndA F (placeAtInf F w a * placeAtInf F w b) =
        sndA F (placeAtInf F w a) * sndA F (placeAtInf F w b) := map_mul (sndA F) _ _
    exact (sndA_placeAtInf F w (a * b)).trans ((mul_zero (0 : Af F)).symm.trans
      (e2.trans (congrArg₂ (· * ·) (sndA_placeAtInf F w a) (sndA_placeAtInf F w b))).symm)

variable {F w}

theorem idem_mul_placeAtInf {ε : AF F} (hε : IsPlacesIdem {w} ∅ ε) (a : w.Completion) :
    ε * placeAtInf F w a = placeAtInf F w a := by
  apply af_ext
  · have e2 : fstA F (ε * placeAtInf F w a) = fstA F ε * fstA F (placeAtInf F w a) := map_mul (fstA F) _ _
    exact e2.trans ((congrArg (fstA F ε * ·) (fstA_placeAtInf F w a)).trans
      ((ainf_idem_mul F w _ (hε.1 w (Finset.mem_singleton_self w))
        (fun u hu => hε.2.1 u (by simpa using hu)) a).trans (fstA_placeAtInf F w a).symm))
  · have e2 : sndA F (ε * placeAtInf F w a) = sndA F ε * sndA F (placeAtInf F w a) := map_mul (sndA F) _ _
    exact e2.trans ((congrArg (sndA F ε * ·) (sndA_placeAtInf F w a)).trans
      ((mul_zero _).trans (sndA_placeAtInf F w a).symm))

theorem placeAtInf_one {ε : AF F} (hε : IsPlacesIdem {w} ∅ ε) : placeAtInf F w 1 = ε := by
  apply af_ext
  · refine (fstA_placeAtInf F w 1).trans ?_
    exact ainf_single_one F w _ (hε.1 w (Finset.mem_singleton_self w))
      (fun u hu => hε.2.1 u (by simpa using hu))
  · refine (sndA_placeAtInf F w 1).trans ?_
    exact (af_zero F _ (fun v => hε.2.2.2 v (Finset.notMem_empty v))).symm

variable (F w) (E : Type) [Field E] [Algebra F E]

def placeAtInfE : w.Completion ⊗[F] E →ₗ[F] AF F ⊗[F] E :=
  LinearMap.rTensor E (placeAtInf F w)

theorem placeAtInfE_tmul (a : w.Completion) (e : E) :
    placeAtInfE F w E (a ⊗ₜ e) = placeAtInf F w a ⊗ₜ e := rfl

theorem placeAtInfE_mul (x y : w.Completion ⊗[F] E) :
    placeAtInfE F w E (x * y) = placeAtInfE F w E x * placeAtInfE F w E y := by
  induction x using TensorProduct.induction_on with
  | zero => rw [zero_mul, map_zero, zero_mul]
  | add a b ha hb => rw [add_mul, map_add (f := _), map_add (f := _), ha, hb, add_mul]
  | tmul a e =>
    induction y using TensorProduct.induction_on with
    | zero => rw [mul_zero, map_zero, mul_zero]
    | add c d hc hd => rw [mul_add, map_add (f := _), map_add (f := _), hc, hd, mul_add]
    | tmul b f =>
      unfold placeAtInfE
      rw [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
        LinearMap.rTensor_tmul, Algebra.TensorProduct.tmul_mul_tmul, placeAtInf_mul]

theorem placeAtInfE_sig (σ : E →ₐ[F] E) (x : w.Completion ⊗[F] E) :
    placeAtInfE F w E (sigR w.Completion σ x) = sigR (AF F) σ (placeAtInfE F w E x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp only [map_add (f := _), h₁, h₂]
  | tmul a e =>
    simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      AlgHom.coe_id, id_eq, placeAtInfE_tmul]

variable {F w E}

theorem idem_mul_placeAtInfE {ε : AF F} (hε : IsPlacesIdem {w} ∅ ε) (x : w.Completion ⊗[F] E) :
    algebraMap (AF F) (AF F ⊗[F] E) ε * placeAtInfE F w E x = placeAtInfE F w E x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp only [mul_add, map_add (f := _), h₁, h₂]
  | tmul a e =>
    rw [placeAtInfE_tmul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, Algebra.algebraMap_self, RingHom.id_apply, idem_mul_placeAtInf hε]

theorem placeAtInfE_incl {ε : AF F} (hε : IsPlacesIdem {w} ∅ ε) (c : E) :
    placeAtInfE F w E (inclR w.Completion c) = algebraMap (AF F) (AF F ⊗[F] E) ε * inclR (AF F) c := by
  simp only [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
    placeAtInfE_tmul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    mul_one, Algebra.algebraMap_self, RingHom.id_apply, placeAtInf_one hε]

theorem normEq_inf_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (w : InfinitePlace F) (ε : AF F), IsPlacesIdem {w} ∅ ε → ∀ c : E,
    (∃ t : w.Completion ⊗[F] E, t * sigR w.Completion σ t + inclR w.Completion c = 0) →
    ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) c) = 0 := by
  intro F E _ _ _ _ σ w ε hε c ⟨t, ht⟩
  refine ⟨placeAtInfE F w E t, ?_⟩
  rw [← placeAtInfE_sig, ← placeAtInfE_mul, mul_add, idem_mul_placeAtInfE hε, ← placeAtInfE_incl hε,
    ← map_add, ht, map_zero]

end GlobalTheory
end
end

section

open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap

theorem _root_.GlobalTheory.T.schrodinger_orthogonality_relation : ∀ (n : ℕ) (f g g' : Sch (Fin n)) (x : EuclideanSpace ℝ (Fin n)),
    ∫ w : Fin n ⊕ Fin n → ℝ, starRingEnd ℂ (∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)) * rhoFun w ⇑f x =
      (∫ t, f t * starRingEnd ℂ (g t)) * g' x := by
  first | exact @GlobalTheory.MoyalPointwise.moyal_pointwise | exact GlobalTheory.MoyalPointwise.moyal_pointwise | (intros; apply GlobalTheory.MoyalPointwise.moyal_pointwise <;> assumption)
end

section

open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil

theorem _root_.GlobalTheory.T.exists_continuous_symplecticHom_of_indefiniteUnitary : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ℕ)
    (φ : (ι → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ (G : Type) [Group G] [TopologicalSpace G] (k : G →* (ι → Mat R S)), Continuous k →
    (∀ g w, (k g w)ᴴ * Jm R S * k g w = Jm R S) →
    ∃ s : G →* Matrix.symplecticGroup l ℝ, Continuous s ∧
      ∀ g c, (s g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ φ c = φ fun w => c w * (k g w)ᵀ := by
  first | exact @GlobalTheory.ColAction.exists_symplectic_hom_of_unitary | exact GlobalTheory.ColAction.exists_symplectic_hom_of_unitary | (intros; apply GlobalTheory.ColAction.exists_symplectic_hom_of_unitary <;> assumption)
end
