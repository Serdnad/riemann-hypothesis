module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle464
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle466
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle467
public import GroundTheory.AutomorphicForms.ReductionHeight
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEpsilonCentralizerBound
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle465
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle408
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwLMulSelf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DefsPlus
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLoc

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

theorem _root_.GlobalTheory.T.range_isotropic_iff_involution_mul_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E) (π : Matrix (Fin n) (Fin n) E), LinearMap.range (Matrix.toLin' π) ≤ perpD (conjE E) d (LinearMap.range (Matrix.toLin' π)) ↔ sg d π * π = 0 := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.iso_range_iff_sg_mul | exact GlobalTheory.CompanionTheory.TorusCh.iso_range_iff_sg_mul | (intros; apply GlobalTheory.CompanionTheory.TorusCh.iso_range_iff_sg_mul <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

theorem _root_.GlobalTheory.T.exists_involution_adjoin_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E), ∃ σ : Algebra.adjoin E {(nrm d).val} →+* Algebra.adjoin E {(nrm d).val}, (∀ x, ((σ x : Algebra.adjoin E {(nrm d).val}) : Matrix (Fin n) (Fin n) E) = sg d x) ∧ ∀ x, σ (σ x) = x := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.SgRing.exists_sgRing | exact GlobalTheory.CompanionTheory.TorusCh.SgRing.exists_sgRing | (intros; apply GlobalTheory.CompanionTheory.TorusCh.SgRing.exists_sgRing <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

theorem _root_.GlobalTheory.T.exists_polynomial_projection_invariant : ∀ (K : Type) [Field K] (n : ℕ) (γ : Matrix (Fin n) (Fin n) K) (v : Fin n → K), γ.charpoly.Separable → (∀ y : Fin n → K, ∃ h : K[X], y = aeval γ h *ᵥ v) → ∀ W : Submodule K (Fin n → K), W.map (Matrix.toLin' γ) ≤ W → ∃ π, IsPol γ π ∧ π * π = π ∧ LinearMap.range (Matrix.toLin' π) = W := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.exists_idem_pol_range_eq | exact GlobalTheory.CompanionTheory.TorusCh.exists_idem_pol_range_eq | (intros; apply GlobalTheory.CompanionTheory.TorusCh.exists_idem_pol_range_eq <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

theorem _root_.GlobalTheory.T.exists_primitive_idempotents_separating : ∀ (K : Type) [Field K] (n : ℕ) (γ : Matrix (Fin n) (Fin n) K), γ.charpoly.Separable → ∃ S : Finset (Matrix (Fin n) (Fin n) K), (∀ e ∈ S, IsPrim γ e) ∧ ∀ x : Fin n → K, x ≠ 0 → ∃ e ∈ S, x ᵥ* e ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.exists_prim_cover | exact GlobalTheory.CompanionTheory.TorusCh.exists_prim_cover | (intros; apply GlobalTheory.CompanionTheory.TorusCh.exists_prim_cover <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

theorem _root_.GlobalTheory.T.degree_mul_idempotent_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), DegAdelic → ∀ (e : Matrix (Fin n) (Fin n) E), e * e = e → ∀ t x : GA E n, t.val * rm e = rm e * t.val → deg (t * x) (LinearMap.range (Matrix.toLin' e)) = deg x (LinearMap.range (Matrix.toLin' e)) + lam e t := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.DegLam.deg_lam | exact GlobalTheory.CompanionTheory.TorusCh.DegLam.deg_lam | (intros; apply GlobalTheory.CompanionTheory.TorusCh.DegLam.deg_lam <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

theorem _root_.GlobalTheory.T.commute_polynomial_of_mem_centralizer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E) (t : GA E n), t ∈ adCent d → ∀ e : Matrix (Fin n) (Fin n) E, IsPol (nrm d).val e → t.val * rm e = rm e * t.val := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.CommMem.adCent_comm_rm | exact GlobalTheory.CompanionTheory.TorusCh.CommMem.adCent_comm_rm | (intros; apply GlobalTheory.CompanionTheory.TorusCh.CommMem.adCent_comm_rm <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

theorem _root_.GlobalTheory.T.exists_epsilon_centralizer_bound : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (γ : Matrix (Fin n) (Fin n) K) (v : Fin n → K), (∀ y : Fin n → K, ∃ h : K[X], y = v ᵥ* aeval γ h) → ∀ e : Matrix (Fin n) (Fin n) K, IsPrim γ e → ∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ ∀ g : GroundTheory.Automorphic.AdelicGLn.AdelicGL K n, g.val * γ.map (algebraMap K (AdeleRing (𝓞 K) K)) = γ.map (algebraMap K (AdeleRing (𝓞 K) K)) * g.val → ∀ s : (AdeleRing (𝓞 K) K)ˣ, (s : AdeleRing (𝓞 K) K) = (1 + e.map (algebraMap K (AdeleRing (𝓞 K) K)) * (g.val - 1)).det → c ≤ (GroundTheory.Global.IdeleGroup.ideleModule K s : ℝ) → ∀ x : Fin n → K, x ᵥ* e ≠ 0 → ε ≤ GroundTheory.Automorphic.Reduction.height g x := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.HeightBound.exists_pos_le_height | exact GlobalTheory.CompanionTheory.TorusCh.HeightBound.exists_pos_le_height | (intros; apply GlobalTheory.CompanionTheory.TorusCh.HeightBound.exists_pos_le_height <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

theorem _root_.GlobalTheory.T.continuousOn_lambda_subgroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (e : Matrix (Fin n) (Fin n) E), e * e = e → (∀ s : (Ad E)ˣ, logAbs (s : Ad E) = Real.log (GroundTheory.Global.IdeleGroup.ideleModule E s : ℝ)) → ∀ H : Subgroup (GA E n), (∀ t ∈ H, t.val * rm e = rm e * t.val) → ContinuousOn (lam e) (H : Set (GA E n)) := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.continuousOn_lam | exact GlobalTheory.CompanionTheory.TorusCh.continuousOn_lam | (intros; apply GlobalTheory.CompanionTheory.TorusCh.continuousOn_lam <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.CTFin.Slice1.Height
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}

theorem norm_one_le : ‖(1 : Cinf E)‖ ≤ 1 := by
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by simp

theorem norm_lev_le (y : GL (Fin r) (Cinf E)) :
    ‖toL (lev (Cinf E) r s (y, 1)).val‖ ≤ ‖toL y.val‖ + 1 := by
  have n0 := norm_nonneg (toL y.val)
  have hent : ∀ i j, ‖(y.val i j : Cinf E)‖ ≤ ‖toL y.val‖ := fun i j =>
    (norm_le_pi_norm (toL y.val i) j).trans (norm_le_pi_norm (toL y.val) i)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i =>
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  change ‖((lev (Cinf E) r s (y, 1) : GL _ _) : Matrix _ _ (Cinf E)) i j‖ ≤ _
  have hv : ((lev (Cinf E) r s (y, 1) : GL _ _) : Matrix _ _ (Cinf E)) =
      Matrix.reindex (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))
        (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))
        (Matrix.fromBlocks y.val 0 0 (1 : Matrix (Fin s) (Fin s) (Cinf E))) := by
    ext i j
    obtain ⟨a, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i
    obtain ⟨b, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases a with a | a <;> rcases b with b | b <;>
      simp [lev, GlobalTheory.SmGL.emb₂, GlobalTheory.SmGL.leviEmb,
        GlobalTheory.SmGL.leviTwo, GlobalTheory.SmGL.two, Matrix.blockDiagonal'_apply]
  rw [hv]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i = i'
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j = j'
  rcases i' with i' | i' <;> rcases j' with j' | j'
  · simpa using (hent i' j').trans (by linarith)
  · simp; linarith
  · simp; linarith
  · have h1 : ‖((1 : Matrix (Fin s) (Fin s) (Cinf E)) i' j')‖ ≤ 1 := by
      by_cases h : i' = j'
      · subst h; simpa using norm_one_le
      · simp [Matrix.one_apply_ne h]
    simpa using h1.trans (by linarith)

theorem height_lev_le (y : GL (Fin r) (Cinf E)) :
    height (lev (Cinf E) r s (y, 1)) ≤ 3 * height y := by
  have e : (lev (Cinf E) r s (y, 1))⁻¹ = lev (Cinf E) r s (y⁻¹, 1) := by
    rw [← map_inv, Prod.inv_mk, inv_one]
  have h1 := norm_lev_le (s := s) y
  have h2 := norm_lev_le (s := s) y⁻¹
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  unfold height
  rw [e]
  linarith

end GlobalTheory.CompanionTheory.CTFin.Slice1.Height

theorem GlobalTheory.CompanionTheory.CTFin.Slice1.height_lev_mul_le : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (c : GL (Fin (r + s)) (Cinf E)), ∃ B : ℝ, 0 ≤ B ∧ ∀ y : GL (Fin r) (Cinf E), height (lev (Cinf E) r s (y, 1) * c) ≤ B * height y := by
  intro E _ _ _ r s c
  have hb : 0 ≤ GlobalTheory.CompanionTheory.GrowthConv.bnd c := by
    unfold GlobalTheory.CompanionTheory.GrowthConv.bnd
    positivity
  refine ⟨3 * GlobalTheory.CompanionTheory.GrowthConv.bnd c, by positivity, fun y => ?_⟩
  refine (GlobalTheory.CompanionTheory.GrowthConv.height_mul_le_bnd c _).trans ?_
  have := mul_le_mul_of_nonneg_left (Height.height_lev_le (s := s) y) hb
  linarith

end
end

section

open Finset PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.LvChain
open CompanionTheory.D.LK (Pos)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.LvStableChains

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def chainsInL (lev : Fin n → ℕ) (d : ℕ) (S : Submodule ℂ V) : Submodule ℂ (Cq n V) where
  carrier := {x | SuppL (inUU lev) x ∧ DegL d x ∧ ∀ A, x A ∈ S}
  add_mem' := by
    rintro x y ⟨hx1, hx2, hx3⟩ ⟨hy1, hy2, hy3⟩
    have key : ∀ A, (x + y) A ≠ 0 → x A ≠ 0 ∨ y A ≠ 0 := fun A h => by
      by_contra hc
      push Not at hc
      exact h (by simp [hc.1, hc.2])
    refine ⟨fun A h => ?_, fun A h => ?_, fun A => S.add_mem (hx3 A) (hy3 A)⟩
    · rcases key A h with h' | h'
      · exact hx1 A h'
      · exact hy1 A h'
    · rcases key A h with h' | h'
      · exact hx2 A h'
      · exact hy2 A h'
  zero_mem' := ⟨fun A h => absurd rfl h, fun A h => absurd rfl h, fun A => S.zero_mem⟩
  smul_mem' := by
    rintro c x ⟨hx1, hx2, hx3⟩
    have key : ∀ A, (c • x) A ≠ 0 → x A ≠ 0 := fun A h h0 => h (by simp [h0])
    exact ⟨fun A h => hx1 A (key A h), fun A h => hx2 A (key A h), fun A => S.smul_mem c (hx3 A)⟩

theorem finiteDimensional_chainsInL (lev : Fin n → ℕ) (d : ℕ) (S : Submodule ℂ V) [FiniteDimensional ℂ S] :
    FiniteDimensional ℂ (chainsInL lev d S) := by
  let L : chainsInL lev d S →ₗ[ℂ] (Finset (Lt n) → S) :=
    LinearMap.pi fun A => LinearMap.codRestrict S ((LinearMap.proj A).comp (chainsInL lev d S).subtype)
      fun x => x.2.2.2 A
  refine Module.Finite.of_injective L fun x y h => Subtype.ext (funext fun A => ?_)
  exact congrArg Subtype.val (congrFun h A)

theorem Lv_apply (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) (x : Cq n V)
    (A : Finset (Lt n)) :
    Lv lev E1 E2 p q x A = kA E1 E2 p q (x A) +
      ∑ l : Lt n, ∑ k : Lt n, if inUU lev l then adCL false p q l k • creL k (annL l x) A else 0 := by
  simp only [Lv, adLL, LinearMap.add_apply, LinearMap.sum_apply, Pi.add_apply, Finset.sum_apply, liftL_apply]
  congr 1
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp [Module.End.mul_apply]

theorem creL_annL_mem {S : Submodule ℂ V} {x : Cq n V} (hx : ∀ A, x A ∈ S) (l k : Lt n) (A : Finset (Lt n)) :
    creL k (annL l x) A ∈ S := by
  rw [creL_apply]
  split_ifs
  · refine S.smul_mem _ ?_
    rw [annL_apply]
    split_ifs
    · exact S.zero_mem
    · exact S.smul_mem _ (hx _)
  · exact S.zero_mem

theorem inUU_of_adCL {lev : Fin n → ℕ} {p q : Fin n} (hpq : lev p = lev q) {l k : Lt n}
    (h : adCL false p q l k ≠ 0) (hl : inUU lev l) : inUU lev k := by
  by_cases c1 : q = l.2.1.1 ∧ k.1 = (false ^^ l.1) ∧ k.2.1 = (p, l.2.1.2)
  · show lev k.2.1.1 < lev k.2.1.2
    rw [c1.2.2]
    show lev p < lev l.2.1.2
    rw [hpq, c1.1]
    exact hl
  by_cases c2 : l.2.1.2 = p ∧ k.1 = (false ^^ l.1) ∧ k.2.1 = (l.2.1.1, q)
  · show lev k.2.1.1 < lev k.2.1.2
    rw [c2.2.2]
    show lev l.2.1.1 < lev q
    rw [← hpq, ← c2.1]
    exact hl
  · exact absurd (by rw [adCL, if_neg c1, if_neg c2, sub_zero]) h

theorem Lv_ne {lev : Fin n → ℕ} {E1 E2 : Fin n → Fin n → Module.End ℂ V} {p q : Fin n} {x : Cq n V}
    {A : Finset (Lt n)} (h : Lv lev E1 E2 p q x A ≠ 0) :
    kA E1 E2 p q (x A) ≠ 0 ∨ ∃ l k, inUU lev l ∧ adCL false p q l k ≠ 0 ∧ creL k (annL l x) A ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  rw [Lv_apply, hc.1, zero_add]
  refine Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun k _ => ?_
  split_ifs with hl
  · by_cases h0 : adCL false p q l k = 0
    · rw [h0, zero_smul]
    · rw [hc.2 l k hl h0, smul_zero]
  · rfl

theorem term_suppL {lev : Fin n → ℕ} {d : ℕ} {p q : Fin n} (hpq : lev p = lev q) {x : Cq n V}
    (hx : SuppL (inUU lev) x) (hd : DegL d x) {A : Finset (Lt n)} {l k : Lt n} (h0 : adCL false p q l k ≠ 0)
    (h : creL k (annL l x) A ≠ 0) : (∀ j ∈ A, inUU lev j) ∧ A.card = d := by
  obtain ⟨hk, h1⟩ := creL_ne h
  obtain ⟨h2, h3⟩ := annL_ne h1
  have hs := hx _ h3
  have hi : inUU lev l := hs l (mem_insert_self _ _)
  refine ⟨fun j hj => ?_, ?_⟩
  · by_cases e : j = k
    · exact e ▸ inUU_of_adCL hpq h0 hi
    · exact hs j (mem_insert_of_mem (mem_erase.2 ⟨e, hj⟩))
  · have e1 := hd _ h3
    rw [card_insert_of_notMem h2] at e1
    have e2 := card_erase_add_one hk
    omega

theorem Lv_mem_chainsInL {lev : Fin n → ℕ} {d : ℕ} {E1 E2 : Fin n → Fin n → Module.End ℂ V}
    {S : Submodule ℂ V} (hS : ∀ a b, ∀ w ∈ S, kA E1 E2 a b w ∈ S) {p q : Fin n} (hpq : lev p = lev q)
    {x : Cq n V} (hx : x ∈ chainsInL lev d S) : Lv lev E1 E2 p q x ∈ chainsInL lev d S := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  have hk : ∀ A, kA E1 E2 p q (x A) ≠ 0 → x A ≠ 0 := fun A h h0 => h (by rw [h0, map_zero])
  refine ⟨fun A h => ?_, fun A h => ?_, fun A => ?_⟩
  · rcases Lv_ne h with h' | ⟨l, k, -, h0, h'⟩
    · exact hx1 A (hk A h')
    · exact (term_suppL hpq hx1 hx2 h0 h').1
  · rcases Lv_ne h with h' | ⟨l, k, -, h0, h'⟩
    · exact hx2 A (hk A h')
    · exact (term_suppL hpq hx1 hx2 h0 h').2
  · rw [Lv_apply]
    refine S.add_mem (hS p q _ (hx3 A)) (S.sum_mem fun l _ => S.sum_mem fun k _ => ?_)
    split_ifs
    · exact S.smul_mem _ (creL_annL_mem hx3 l k A)
    · exact S.zero_mem

theorem exists_stable : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) (d : ℕ) (y : Cq n V),
    (∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kA E1 E2 a b w ∈ S) →
    SuppL (inUU lev) y → DegL d y →
    ∃ T : Submodule ℂ (Cq n V), FiniteDimensional ℂ T ∧ y ∈ T ∧ (∀ x ∈ T, SuppL (inUU lev) x ∧ DegL d x) ∧
      ∀ p q : Fin n, lev p = lev q → ∀ x ∈ T, Lv lev E1 E2 p q x ∈ T := by
  intro n lev V _ _ E1 E2 d y hF hy hd
  choose Sf hfd hmem hSt using hF
  let S : Submodule ℂ V := ⨆ A, Sf (y A)
  have : ∀ A, FiniteDimensional ℂ (Sf (y A)) := fun A => hfd _
  have : FiniteDimensional ℂ S := Submodule.finiteDimensional_iSup _
  have hSs : ∀ a b, ∀ w ∈ S, kA E1 E2 a b w ∈ S := fun a b v hv =>
    (iSup_le fun A z hz => Submodule.mem_iSup_of_mem A (hSt _ a b z hz) : S ≤ S.comap (kA E1 E2 a b)) hv
  refine ⟨chainsInL lev d S, finiteDimensional_chainsInL lev d S,
    ⟨hy, hd, fun A => Submodule.mem_iSup_of_mem A (hmem _)⟩, fun x hx => ⟨hx.1, hx.2.1⟩,
    fun p q hpq x hx => Lv_mem_chainsInL hSs hpq hx⟩

end GlobalTheory.CompanionTheory.LvStableChains
end
end

section

open Finset PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.LvChain
open CompanionTheory.D.LK (Pos)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.LvChain

theorem adCL_mem_omU {n : ℕ} {lev : Fin n → ℕ} {p q : Fin n} (hpq : p < q) (hl : lev p = lev q) {l k : Lt n}
    (hc : adCL false p q l k ≠ 0) (hm : l ∈ omU lev) : k ∈ omU lev ∧ k ≠ l := by
  have hcase : (q = l.2.1.1 ∧ k.1 = xor false l.1 ∧ k.2.1 = (p, l.2.1.2)) ∨
      (l.2.1.2 = p ∧ k.1 = xor false l.1 ∧ k.2.1 = (l.2.1.1, q)) := by
    by_contra hn
    rw [not_or] at hn
    exact hc (by simp only [adCL, if_neg hn.1, if_neg hn.2, sub_self])
  obtain ⟨h1, h2⟩ : l.1 = false ∧ lev l.2.1.1 < lev l.2.1.2 := (mem_filter.1 hm).2
  have hne : p ≠ q := ne_of_lt hpq
  rcases hcase with ⟨e1, e0, e2⟩ | ⟨e1, e0, e2⟩
  · refine ⟨mem_filter.2 ⟨mem_univ _, ?_, ?_⟩, fun e => ?_⟩
    · rw [e0, h1]; rfl
    · rw [e2]; show lev p < lev l.2.1.2; rw [hl, e1]; exact h2
    · rw [e] at e2; exact hne (e1.trans (congrArg Prod.fst e2)).symm
  · refine ⟨mem_filter.2 ⟨mem_univ _, ?_, ?_⟩, fun e => ?_⟩
    · rw [e0, h1]; rfl
    · rw [e2]; show lev l.2.1.1 < lev q; rw [← hl, ← e1]; exact h2
    · rw [e] at e2; exact hne (e1.symm.trans (congrArg Prod.snd e2))

theorem Lv_single_omU : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) (u : V),
    (∀ a b : Fin n, a < b → kA E1 E2 a b u = 0) → ∀ p q : Fin n, p < q → lev p = lev q →
      Lv lev E1 E2 p q (Pi.single (omU lev) u : Cq n V) = 0 := by
  intro n lev V _ _ E1 E2 u hu p q hpq hl
  have h1 : liftL n (kA E1 E2 p q) (Pi.single (omU lev) u : Cq n V) = 0 := by
    funext A
    rw [liftL_apply]
    by_cases e : A = omU lev
    · subst e
      rw [Pi.single_eq_same]
      exact hu p q hpq
    · rw [Pi.single_eq_of_ne e, map_zero]
      rfl
  have h2 : adLL lev false p q (Pi.single (omU lev) u : Cq n V) = 0 := by
    simp only [adLL, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun k _ => ?_
    split_ifs with hS
    swap
    · rfl
    by_cases hc : adCL false p q l k = 0
    · rw [hc, zero_smul]; rfl
    suffices h : creL k (annL l (Pi.single (omU lev) u : Cq n V)) = 0 by
      rw [LinearMap.smul_apply, Module.End.mul_apply, h, smul_zero]
    funext B
    by_contra h
    obtain ⟨-, h3⟩ := creL_ne h
    obtain ⟨-, h4⟩ := annL_ne h3
    have e : insert l (B.erase k) = omU lev := by
      by_contra h'
      exact h4 (Pi.single_eq_of_ne h' _)
    have hm : l ∈ omU lev := e ▸ mem_insert_self _ _
    obtain ⟨hk, hkl⟩ := adCL_mem_omU hpq hl hc hm
    rw [← e] at hk
    rcases mem_insert.1 hk with h5 | h5
    · exact hkl h5
    · exact notMem_erase _ _ h5
  show liftL n (kA E1 E2 p q) _ + adLL lev false p q _ = 0
  rw [h1, h2, add_zero]

end GlobalTheory.CompanionTheory.LvChain
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels PositivityTheory.SiegelWeilFormula

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelRadTop

theorem nA_top : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ),
    (∀ β : Matrix (Fin n) (Fin n) (AE F E), β ∈ nA σ Y b ↔ βᵀ + ((ε : ℤ) : AE F E) • β.map (cA σ) = 0) →
    IsClosed (nA σ Y b : Set (Matrix (Fin n) (Fin n) (AE F E))) ∧ IsTopologicalAddGroup (nA σ Y b) ∧
    LocallyCompactSpace (nA σ Y b) ∧ SecondCountableTopology (nA σ Y b) ∧ T2Space (nA σ Y b) ∧ BorelSpace (nA σ Y b) := by
  intro F E _ _ _ _ _ σ n Y b ε h
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : BorelSpace (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (BorelSpace (Fin n → Fin n → AE F E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AE F E))
  have hc : Continuous (cA σ) :=
    IsModuleTopology.continuous_of_linearMap (R := AF F) (cA σ).toLinearMap
  have hS : (nA σ Y b : Set (Matrix (Fin n) (Fin n) (AE F E))) =
      {β | βᵀ + ((ε : ℤ) : AE F E) • β.map (cA σ) = 0} := Set.ext h
  have hC : IsClosed (nA σ Y b : Set (Matrix (Fin n) (Fin n) (AE F E))) := by
    rw [hS]
    have h1 : Continuous fun β : Matrix (Fin n) (Fin n) (AE F E) => β.map (cA σ) := continuous_id.matrix_map hc
    have h2 : Continuous fun β : Matrix (Fin n) (Fin n) (AE F E) => ((ε : ℤ) : AE F E) • β.map (cA σ) :=
      (continuous_const_smul (((ε : ℤ) : AE F E))).comp h1
    exact isClosed_eq (continuous_id.matrix_transpose.add h2) continuous_const
  haveI : LocallyCompactSpace (nA σ Y b) := hC.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (nA σ Y b) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  exact ⟨hC, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

end GlobalTheory.CompanionTheory.SiegelRadTop
end
end
