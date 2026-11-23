module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1911
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle069
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterLocalNontrivial
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicHaarFiniteInfiniteProduct
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle075
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle076
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviEqISupParts
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemFormsOnOfMemSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviDecompositionGradedIsotropicFlag
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2159
public import Formalism.SharpRestriction.GlobalSchurBounds.LocalCountingBounds
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

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.adapted_frame_orthogonal_subspace : ∀ (D : D7) (V V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι →
    ∀ (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y →
    ∀ T : Finset (Fin m), (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) →
    ∀ C : GL (Fin V.rank) D.host.E, GlobalTheory.BlockForms.IsAdapted D.sp.cm.sig V.gram X Y C →
    ∀ a : ℕ, a ≤ m → (∀ i : Fin m, i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T ↔ i.val < a) →
    ∃ hdim : a + V'.rank + a = V.rank, ∃ B Bi : Matrix (Fin V'.rank) (Fin V'.rank) D.host.E, B * Bi = 1 ∧
      (∀ (i : Fin V.rank) (j : Fin V'.rank), frameMat V V' ι i j = ∑ r : Fin V'.rank, C.1 i (⟨a + r.val, by omega⟩ : Fin V.rank) * B r j) ∧
      ∀ b : Fin V.rank, (b.val < a ∨ V.rank ≤ b.val + a) →
        (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι) * V.gram) *ᵥ (fun k => C.1 k b) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.ComplFrame.frame_cols | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.ComplFrame.frame_cols | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.ComplFrame.frame_cols <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

theorem _root_.GlobalTheory.T.levi_eq_iSup_parts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ J X Y → ∀ T : Finset (Fin r), levi σ J X Y T = ⨆ i, part σ J X Y T i := by
  first | exact @GlobalTheory.CompanionTheory.LeviGen.levi_eq_iSup_part | exact GlobalTheory.CompanionTheory.LeviGen.levi_eq_iSup_part | (intros; apply GlobalTheory.CompanionTheory.LeviGen.levi_eq_iSup_part <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

theorem _root_.GlobalTheory.T.constant_term_frame_K_type_coefficients : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)) (c : D.what₂.Tau → ℕ → ℂ) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E) (T : Finset (Fin m)) (φ : GA D V → ℂ), φ ∈ cuspOn θ V X Y T U ε fr ρ c → ∀ b : GA D V, (fun x => φ (x * b)) ∈ cuspOn θ V X Y T (U.map (MulAut.conj b).toMonoidHom) ε (fun τ => fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹) ρ c := by
  exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Transl.cuspOn_mul_right
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

theorem _root_.GlobalTheory.T.hermitian_part_le_levi : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E) (T : Finset (Fin m)), uPart D.sp.cm.sig V.gram X Y T ≤ levi D.sp.cm.sig V.gram X Y T := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.uPart_le_levi | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.uPart_le_levi | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.uPart_le_levi <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet


theorem _root_.GlobalTheory.T.levi_inf_unipotent_le_hermitian_part : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (κ : Fin m), κ ∉ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T → levi D.sp.cm.sig V.gram X Y T ⊓ unip D.sp.cm.sig V.gram X (insert κ T) ≤ uPart D.sp.cm.sig V.gram X Y T := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.LeviU.levi_inf_unip_le_uPart | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.LeviU.levi_inf_unip_le_uPart | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.LeviU.levi_inf_unip_le_uPart <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

theorem _root_.GlobalTheory.T.unitary_adelic_unipotent_lift : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n m : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin m) E) (T : Finset (Fin m)) (g : GAd σ J)
    (U : Matrix (Fin m) (Fin n) (AF F ⊗[F] E)) (W : Matrix (Fin n) (Fin m) (AF F ⊗[F] E)),
    Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → (∀ i v, i ∉ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T → U i v = 0) →
    (∀ v i, i ∉ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T → W v i = 0) →
    (∀ i j, j ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T → (U * GlobalTheory.SiegelSet.adMat F X) i j = 0) →
    (GlobalTheory.AdelicU.matHom _ σ J g).1 = 1 + GlobalTheory.SiegelSet.adMat F X * U + W * GlobalTheory.SiegelSet.adMat F (Formalism.UG.cT (σ : E →+* E) X * J) →
    g ∈ GlobalTheory.StdPar.unip σ J X T := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.UnipCrit.mem_unip | exact GlobalTheory.CompanionTheory.Hypotheses₂.UnipCrit.mem_unip | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.UnipCrit.mem_unip <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet


theorem _root_.GlobalTheory.T.exists_orthogonal_hermitian_subspace : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ T : Finset (Fin m), ∃ (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι ∧ ∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0 := by
  first | exact @GlobalTheory.CompanionTheory.WittCompl.exists_compl | exact GlobalTheory.CompanionTheory.WittCompl.exists_compl | (intros; apply GlobalTheory.CompanionTheory.WittCompl.exists_compl <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

theorem _root_.GlobalTheory.T.levi_parts_commute : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ J X Y → ∀ T : Finset (Fin r), Pairwise fun i j : Option {k // k ∈ T} => ∀ x y : GAd σ J, x ∈ part σ J X Y T i → y ∈ part σ J X Y T j → Commute x y := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Comm.part_commute | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Comm.part_commute | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Comm.part_commute <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
open GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.Down

section Core

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev adV {n : ℕ} (v : Fin n → E) : Fin n → AF F ⊗[F] E := fun i => inclR (F := F) (AF F) (v i)

theorem adMat_mulVec {a c : ℕ} (M : Matrix (Fin a) (Fin c) E) (v : Fin c → E) :
    adMat F M *ᵥ adV (F := F) v = adV (F := F) (M *ᵥ v) :=
  funext fun i => (RingHom.map_mulVec (inclR (F := F) (AF F)) M v i).symm

theorem core (σ : E →ₐ[F] E) {n n' r r' : ℕ} {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin n') (Fin n') E}
    {X : Matrix (Fin n) (Fin r) E} {X' Y' : Matrix (Fin n') (Fin r') E} {T : Finset (Fin r)} {e : Fin r' → Fin r}
    {I : Matrix (Fin n) (Fin n') E} {P : Matrix (Fin n') (Fin n) E}
    (hmono : StrictMono e) (hrange : ∀ i, i ∉ upTo T ↔ i ∈ Set.range e)
    (hIX : I * X' = X.submatrix id e) (hPI : P * I = 1)
    (hg : Formalism.UG.cT (σ : E →+* E) I * J = J' * P)
    (hPl : ∀ l ∈ upTo T, P *ᵥ Xᵀ l = 0)
    (hperp : ∀ x, ∀ l ∈ upTo T, ((Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ (I *ᵥ x)) l = 0)
    (hW' : IsWittFrame σ J' X' Y') (k : Fin r') (g : GAd σ J) (b : GAd σ J')
    (hmat : (matHom _ σ J g).1 = 1 + adMat F I * ((matHom _ σ J' b).1 - 1) * adMat F P)
    (hgm : g ∈ unip σ J X (insert (e k) T)) : b ∈ unip σ J' X' {k} := by
  obtain ⟨M, hM⟩ : ∃ M, M = (matHom _ σ J' b).1 - 1 := ⟨_, rfl⟩
  rw [← hM] at hmat
  have hPI' : adMat F P * adMat F I = 1 := by
    rw [← Matrix.map_mul, hPI, Matrix.map_one _ (map_zero _) (map_one _)]
  have hPIv : ∀ w, adMat F P *ᵥ (adMat F I *ᵥ w) = w := fun w => by rw [mulVec_mulVec, hPI', one_mulVec]
  have hGv : ∀ w, (matHom _ σ J g).1 *ᵥ (adMat F I *ᵥ w) - adMat F I *ᵥ w = adMat F I *ᵥ (M *ᵥ w) := fun w => by
    rw [hmat, Matrix.add_mulVec, one_mulVec, add_sub_cancel_left, ← Matrix.mulVec_mulVec, hPIv, ← Matrix.mulVec_mulVec]
  have hXe : ∀ i, (adMat F X)ᵀ (e i) = adMat F I *ᵥ (adMat F X')ᵀ i := fun i => by
    have h : adMat F I * adMat F X' = adMat F (X.submatrix id e) := by rw [← Matrix.map_mul, hIX]
    funext j
    exact (congrFun (congrFun h j) i).symm
  have hPX : ∀ l ∈ upTo T, adMat F P *ᵥ (adMat F X)ᵀ l = 0 := fun l hl => by
    change adMat F P *ᵥ adV (F := F) (Xᵀ l) = 0
    rw [adMat_mulVec, hPl l hl]
    funext i
    exact map_zero _
  have hPspan : ∀ (A : Set (Fin r)) (N : Submodule (AF F ⊗[F] E) (Fin n' → AF F ⊗[F] E)),
      (∀ i ∈ A, adMat F P *ᵥ (adMat F X)ᵀ i ∈ N) → ∀ y ∈ colSpan F X A, adMat F P *ᵥ y ∈ N := fun A N h y hy => by
    have h1 : colSpan F X A ≤ N.comap (adMat F P).mulVecLin :=
      Submodule.span_le.2 (by rintro _ ⟨i, hi, rfl⟩; exact h i hi)
    exact h1 hy
  have ha : ∀ i : Fin r', i ≤ k → M *ᵥ (adMat F X')ᵀ i = 0 := fun i hi => by
    have h1 := (Subgroup.mem_iInf.1 hgm.1 (e i)).2 ((adMat F X)ᵀ (e i)) (Submodule.subset_span ⟨e i, rfl, rfl⟩)
    rw [hXe, hGv] at h1
    have h2 := hPspan _ ⊥ (fun l hl => by
      obtain ⟨k', hk', hlk, hkj⟩ := hl
      rcases Finset.mem_insert.1 hk' with rfl | h
      · exact absurd hkj (not_lt.2 (hmono.monotone hi))
      · exact (Submodule.mem_bot _).2 (hPX l ⟨k', h, hlk⟩)) _ h1
    rw [hPIv] at h2
    exact (Submodule.mem_bot _).1 h2
  have hfix : M * adMat F (initCols X' k) = 0 := Matrix.ext_col fun i =>
    ha (i.castLE k.2) (Nat.le_of_lt_succ i.2)
  have c1 : ∀ {a c : ℕ} (Z : Matrix (Fin a) (Fin c) E), Formalism.UG.cT (sigR (AF F) σ) (adMat F Z) = adMat F (Formalism.UG.cT (σ : E →+* E) Z) :=
    fun Z => rfl
  have fix : (matHom _ σ J' b).1 * adMat F (initCols X' k) = adMat F (initCols X' k) := by
    rw [hM, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hfix
    exact hfix
  rw [unip_singleton hW' k]
  apply Subgroup.subset_closure
  refine ⟨hM ▸ hfix, ?_, fun x hx => ?_⟩
  · have hu : Formalism.UG.cT (sigR (AF F) σ) (matHom _ σ J' b).1 * adMat F J' * (matHom _ σ J' b).1 = adMat F J' := b.2
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero, adMat, Matrix.map_mul]
    change adMat F _ * adMat F J' * _ = adMat F _ * adMat F J'
    conv_lhs => rw [← c1, ← fix, Formalism.UG.cT_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ (adMat F J'), hu, c1]
  · have h5 : Formalism.UG.cT (σ : E →+* E) (X.submatrix id e) * J * I = Formalism.UG.cT (σ : E →+* E) X' * J' := by
      rw [← hIX, Formalism.UG.cT_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ J, hg, Matrix.mul_assoc, hPI,
        Matrix.mul_one]
    have hle : ∀ l, l ∉ upTo T → (∃ k' ∈ insert (e k) T, l ≤ k') → ∃ i, i ≤ k ∧ e i = l := fun l hl ⟨k', hk', hlk⟩ => by
      obtain ⟨i, rfl⟩ := (hrange l).1 hl
      rcases Finset.mem_insert.1 hk' with rfl | h
      · exact ⟨i, hmono.le_iff_le.1 hlk, rfl⟩
      · exact absurd ⟨k', h, hlk⟩ hl
    have hz : ∀ l, (∃ k' ∈ insert (e k) T, l ≤ k') → ((Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ (I *ᵥ x)) l = 0 := fun l hl => by
      by_cases h : l ∈ upTo T
      · exact hperp x l h
      · obtain ⟨i, hi, rfl⟩ := hle l h hl
        rw [mulVec_mulVec]
        have h6 : ((Formalism.UG.cT (σ : E →+* E) X * J * I) *ᵥ x) (e i) = ((Formalism.UG.cT (σ : E →+* E) (X.submatrix id e) * J * I) *ᵥ x) i := rfl
        rw [h6, h5]
        exact congrFun hx ⟨i.val, Nat.lt_succ_of_le hi⟩
    have hp : adV (F := F) (I *ᵥ x) ∈ colPerp σ J X {i | ∃ k' ∈ insert (e k) T, i ≤ k'} := by
      simp only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker]
      intro l hl
      change (adMat F (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ adV (F := F) (I *ᵥ x)) l = 0
      rw [adMat_mulVec]
      change inclR (F := F) (AF F) _ = 0
      rw [hz l hl]
      exact map_zero _
    have h3 := hgm.2.2 _ hp
    rw [← adMat_mulVec, hGv] at h3
    have h4 := hPspan _ (colSpan F X' {i | i ≤ k}) (fun l hl => by
      by_cases h : l ∈ upTo T
      · rw [hPX l h]
        exact zero_mem _
      · obtain ⟨i, hi, rfl⟩ := hle l h hl
        rw [hXe, hPIv]
        exact Submodule.subset_span ⟨i, hi, rfl⟩) _ h3
    rw [hPIv] at h4
    obtain ⟨a, ha'⟩ := mem_colSpan_iff.1 h4
    exact ⟨a, by rw [← hM]; exact ha'.symm⟩

end Core

theorem mem_unip_of_image : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) → ∀ (m' : ℕ) (e : Fin m' → Fin m) (X' Y' : Matrix (Fin V'.rank) (Fin m') D.host.E), GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.IsSliceFrame V V' ι X Y T e X' Y' → GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V'.gram X' Y' → ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) → ∀ k : Fin m', ∀ b : GA D V', s b ∈ unip D.sp.cm.sig V.gram X (insert (e k) T) → b ∈ unip D.sp.cm.sig V'.gram X' {k} := by
  intro D V m X Y hW T V' ι hι hR m' e X' Y' hS hW' s hs k b hb
  obtain ⟨hmono, hrange, hIX, -⟩ := hS
  refine core D.sp.cm.sig hmono hrange hIX (prM_mul_frameMat hι) cT_frameMat_mul_gram (fun l hl => ?_) (fun x l hl => ?_)
    hW' k (s b) b (mat_eq hι hs b) hb
  · exact prM_mulVec_eq_zero fun v' => ((hR (ι v')).1 ⟨v', rfl⟩ l hl).1
  · have hv : ι (V'.frame.equivFun.symm x) = V.frame.equivFun.symm (frameMat V V' ι *ᵥ x) := by
      apply V.frame.equivFun.injective
      rw [LinearEquiv.apply_symm_apply]
      have h := LinearMap.toMatrix_mulVec_repr V'.frame V.frame ι (V'.frame.equivFun.symm x)
      have h' : V'.frame.repr (V'.frame.equivFun.symm x) = x := funext fun i => repr_symm V' x i
      rw [h'] at h
      exact h.symm
    have h := ((hR (ι (V'.frame.equivFun.symm x))).1 ⟨_, rfl⟩ l hl).1
    rw [hv, hT_frame] at h
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_) h
    rfl

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.Down
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin

open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev

theorem ratPts_unip_le_leftSub : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E),
    GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ S T : Finset (Fin m), S ⊆ T →
      GQ V ⊓ unip D.sp.cm.sig V.gram X T ≤ leftSub V X Y S := by
  intro D V m X Y hW S T hST
  have hCM := Formalism.MainNotions.UnusedSlot34.isCMExt_D D
  have hH := Orb.isHermND_gram V
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst hS
    intro g hg
    rw [Subgroup.mem_inf] at hg
    unfold leftSub
    apply Subgroup.mem_sup_right
    refine Subgroup.mem_inf.2 ⟨hg.1, ?_⟩
    simp [GlobalTheory.StdPar.levi]
  · have hkS : S.max' hS ∈ S := S.max'_mem hS
    have hle : ∀ j ∈ S, j ≤ S.max' hS := fun j hj => S.le_max' j hj
    have hs : ((S.max' hS : Fin m) : ℕ) + 1 ≤ m := (S.max' hS).isLt
    have hiff : ∀ i : Fin m, (i : ℕ) < (S.max' hS : ℕ) + 1 ↔ ∃ j ∈ S, i ≤ j := by
      intro i
      constructor
      · intro hi
        exact ⟨S.max' hS, hkS, Fin.le_iff_val_le_val.2 (Nat.lt_succ_iff.1 hi)⟩
      · rintro ⟨j, hj, hij⟩
        have h1 := Fin.le_iff_val_le_val.1 hij
        have h2 := Fin.le_iff_val_le_val.1 (hle j hj)
        omega
    obtain ⟨hU, hL, -⟩ := GlobalTheory.TieStd.stdPar_eq_flag _ _ D.sp.cm.sig hCM _ V.gram hH m X Y hW S (((S.max' hS : Fin m) : ℕ) + 1) hs hiff
      (fun i => ({x ∈ S | x < Fin.castLE hs i} : Finset (Fin m)).card) (fun _ => rfl)
    have hpar := GlobalTheory.ConstTrans.unip_le_parFlag _ _ D.sp.cm.sig hCM _ V.gram hH m X Y hW T S (S.max' hS) hST hkS hle
    have hxx : Formalism.UG.cT (↑D.sp.cm.sig) (X.submatrix id (Fin.castLE hs)) * V.gram * X.submatrix id (Fin.castLE hs) = 0 := by
      ext i j
      have := congrFun (congrFun hW.xx (Fin.castLE hs i)) (Fin.castLE hs j)
      simpa [Formalism.UG.cT, Matrix.mul_apply] using this
    have hyy : Formalism.UG.cT (↑D.sp.cm.sig) (Y.submatrix id (Fin.castLE hs)) * V.gram * Y.submatrix id (Fin.castLE hs) = 0 := by
      ext i j
      have := congrFun (congrFun hW.yy (Fin.castLE hs i)) (Fin.castLE hs j)
      simpa [Formalism.UG.cT, Matrix.mul_apply] using this
    have hxy : Formalism.UG.cT (↑D.sp.cm.sig) (X.submatrix id (Fin.castLE hs)) * V.gram * Y.submatrix id (Fin.castLE hs) = 1 := by
      ext i j
      have := congrFun (congrFun hW.xy (Fin.castLE hs i)) (Fin.castLE hs j)
      simpa [Formalism.UG.cT, Matrix.mul_apply, Matrix.one_apply, Fin.ext_iff] using this
    obtain ⟨hdec, -⟩ := GlobalTheory.LeviFlag.levi_decomposition _ _ D.sp.cm.sig hCM _ V.gram hH _
      (X.submatrix id (Fin.castLE hs)) (Y.submatrix id (Fin.castLE hs))
      (fun i => ({x ∈ S | x < Fin.castLE hs i} : Finset (Fin m)).card) hxx hyy hxy
    intro g hg
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hgQ, hgT⟩ := hg
    have hp := hpar hgT
    obtain ⟨u, hu, l, hl, rfl, hrat⟩ := hdec g hp
    unfold leftSub
    rw [hU, hL]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨hrat hgQ, hl⟩))

end GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin
end
end
