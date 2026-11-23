module

public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle339
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle318
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle385
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GraphElementIwasawaSplitPlace
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepresentationOfEigensystem
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfAutomorphicEmbedding
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle409
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054

@[expose] public section

section

noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice
open Formalism.UG (GLint)

namespace GlobalTheory.GraphNorm

private theorem pairVec_finSumFinEquiv_injective_eq {X : Type} {n : ℕ} {a b c d : Fin n → X}
    (h : pairVec finSumFinEquiv a b = pairVec finSumFinEquiv c d) : a = c ∧ b = d := by
  constructor
  · funext i
    have h' := congrFun h (finSumFinEquiv (.inl i))
    simpa only [pairVec_inl] using h'
  · funext i
    have h' := congrFun h (finSumFinEquiv (.inr i))
    simpa only [pairVec_inr] using h'
theorem unitaryLocalPoint_latticeGraphNorm_identity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F)) (g : GLoc σ J v) (p : siegelH (Fv F v) σ (dblGram finSumFinEquiv J)) (k : GLoc σ (dblGram finSumFinEquiv J) v), k ∈ KFin σ (dblGram finSumFinEquiv J) L v → ioH (Fv F v) σ rfl (g, 1) = (p : GLoc σ (dblGram finSumFinEquiv J) v) * k → ∀ y : Fin n → Fv F v ⊗[F] E, (y ∈ latLoc F L v ∧ y ∈ latMoved σ J L v g) ↔ ∃ x ∈ latLoc F L v, y = (leviOf finSumFinEquiv (matHom (Fv F v) σ (dblGram finSumFinEquiv J)) p).1 *ᵥ x := by
  intro F E _ _ _ _ _ σ h n J hJ L _ v g p k hk hpk y
  simp only [KFin] at hk
  unfold GlobalTheory.AdelicU.stabLoc at hk
  rw [Subgroup.mem_comap, latLoc_sumLat] at hk
  simp only [Formalism.UG.stabGL, Subgroup.mem_mk, Set.mem_setOf_eq, Submonoid.mem_mk, Subsemigroup.mem_mk] at hk
  have hmat : (matHom (Fv F v) σ (dblGram finSumFinEquiv J) (p : GLoc σ (dblGram finSumFinEquiv J) v)).1 *
      (matHom (Fv F v) σ (dblGram finSumFinEquiv J) k).1 =
      blkMat finSumFinEquiv (matHom (Fv F v) σ J g).1 1 := by
    have h1 := congrArg (fun x => (matHom (Fv F v) σ (dblGram finSumFinEquiv J) x).1) hpk
    simp only [map_mul, Units.val_mul, matHom_ioH, val_blkGL, map_one, Units.val_one] at h1
    exact h1.symm
  have hkd : KeepsDiag finSumFinEquiv
      (matHom (Fv F v) σ (dblGram finSumFinEquiv J) (p : GLoc σ (dblGram finSumFinEquiv J) v)).1 :=
    mem_siegelOf.mp p.2
  have hkdi : KeepsDiag finSumFinEquiv (matHom (Fv F v) σ (dblGram finSumFinEquiv J)
      ((p⁻¹ : siegelH (Fv F v) σ (dblGram finSumFinEquiv J)) : GLoc σ (dblGram finSumFinEquiv J) v)).1 :=
    mem_siegelOf.mp (p⁻¹).2
  have hPinv : matHom (Fv F v) σ (dblGram finSumFinEquiv J)
      ((p⁻¹ : siegelH (Fv F v) σ (dblGram finSumFinEquiv J)) : GLoc σ (dblGram finSumFinEquiv J) v) =
      (matHom (Fv F v) σ (dblGram finSumFinEquiv J) (p : GLoc σ (dblGram finSumFinEquiv J) v))⁻¹ := by
    rw [Subgroup.coe_inv, map_inv]
  rw [val_leviOf, mem_latMoved]
  set M := matHom (Fv F v) σ (dblGram finSumFinEquiv J) with hM
  set mJ := matHom (Fv F v) σ J with hmJ
  set S := sumLat finSumFinEquiv (latLoc F L v) (latLoc F L v) with hS
  constructor
  · rintro ⟨hy, hyg⟩
    have hw : pairVec finSumFinEquiv ((mJ g⁻¹).1 *ᵥ y) y ∈ S :=
      (pairVec_mem_sumLat finSumFinEquiv).mpr ⟨hyg, hy⟩
    have hz := (hk _).mp hw
    have hPz : (M (p : GLoc σ (dblGram finSumFinEquiv J) v)).1 *ᵥ ((M k).1 *ᵥ pairVec finSumFinEquiv ((mJ g⁻¹).1 *ᵥ y) y) =
        pairVec finSumFinEquiv y y := by
      rw [Matrix.mulVec_mulVec, hmat, blkMat_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul,
        ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec]
    have hz_eq : (M k).1 *ᵥ pairVec finSumFinEquiv ((mJ g⁻¹).1 *ᵥ y) y =
        pairVec finSumFinEquiv (leviMat finSumFinEquiv (M ((p⁻¹ : siegelH (Fv F v) σ (dblGram finSumFinEquiv J)) :
          GLoc σ (dblGram finSumFinEquiv J) v)).1 *ᵥ y)
          (leviMat finSumFinEquiv (M ((p⁻¹ : siegelH (Fv F v) σ (dblGram finSumFinEquiv J)) :
          GLoc σ (dblGram finSumFinEquiv J) v)).1 *ᵥ y) := by
      rw [← hkdi.mulVec_diag, ← hPz, Matrix.mulVec_mulVec, hPinv, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [hz_eq, pairVec_mem_sumLat] at hz
    refine ⟨_, hz.1, ?_⟩
    have hd := hkd.mulVec_diag (leviMat finSumFinEquiv (M ((p⁻¹ : siegelH (Fv F v) σ (dblGram finSumFinEquiv J)) :
          GLoc σ (dblGram finSumFinEquiv J) v)).1 *ᵥ y)
    rw [← hz_eq, hPz] at hd
    exact (pairVec_finSumFinEquiv_injective_eq hd).1
  · rintro ⟨x, hx, rfl⟩
    have hxx : pairVec finSumFinEquiv x x ∈ S := (pairVec_mem_sumLat finSumFinEquiv).mpr ⟨hx, hx⟩
    obtain ⟨u, hu⟩ : ∃ u, u = (M k⁻¹).1 *ᵥ pairVec finSumFinEquiv x x := ⟨_, rfl⟩
    have hKu : (M k).1 *ᵥ u = pairVec finSumFinEquiv x x := by
      rw [hu, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
        Matrix.one_mulVec]
    have huS : u ∈ S := (hk u).mpr (hKu ▸ hxx)
    have hsplit := (pairVec_eta finSumFinEquiv u).symm
    have hPKu : blkMat finSumFinEquiv (mJ g).1 1 *ᵥ u =
        pairVec finSumFinEquiv (leviMat finSumFinEquiv (M (p : GLoc σ (dblGram finSumFinEquiv J) v)).1 *ᵥ x)
          (leviMat finSumFinEquiv (M (p : GLoc σ (dblGram finSumFinEquiv J) v)).1 *ᵥ x) := by
      rw [← hmat, ← Matrix.mulVec_mulVec, hKu, hkd.mulVec_diag]
    rw [hsplit, blkMat_mulVec, Matrix.one_mulVec] at hPKu
    obtain ⟨h1, h2⟩ := pairVec_finSumFinEquiv_injective_eq hPKu
    rw [hsplit, pairVec_mem_sumLat] at huS
    refine ⟨h2 ▸ huS.2, ?_⟩
    rw [← h1, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
      Matrix.one_mulVec]
    exact huS.1
private theorem exists_isElemDiv {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}
    (x : GL (Fin n) (Fv F v)) : ∃ d : Fin n → (Fv F v)ˣ, IsElemDiv x d := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hv : Valued.v ((π : F) : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hπ
  have hϖ0 : ((π : F) : v.adicCompletion F) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  have hmem : ((π : F) : v.adicCompletion F) ∈ Formalism.UG.Ov F v := by
    show _ ∈ v.adicCompletionIntegers F
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, hv, ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by norm_num)
  obtain ⟨a, -, k₁, hk₁, k₂, hk₂, hx⟩ := Formalism.UG.Final.CartanDecomp F v n _ hmem hv x
  refine ⟨fun i => Units.mk0 (((π : F) : v.adicCompletion F) ^ (a i)) (zpow_ne_zero _ hϖ0), k₁, hk₁, k₂, hk₂, ?_⟩
  rw [hx]
  rfl
private theorem min_self_inv_le_one (a : ℝ≥0) : min a a⁻¹ ≤ 1 := by
  rcases le_total a 1 with h1 | h1
  · exact (min_le_left _ _).trans h1
  · exact (min_le_right _ _).trans (inv_le_one_of_one_le₀ h1)
private theorem natCast_zpow_neg_le_one (N l : ℕ) (hN : 1 ≤ N) : ((N : ℝ≥0)) ^ (-(l : ℤ)) ≤ 1 := by
  rw [zpow_neg, zpow_natCast]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast hN))

theorem graphNormFinite : GraphNormFinite := by
  intro F E _ _ _ _ _ σ h n J hJ L _ v hSD
  refine ⟨?_, ?_⟩
  · intro τ β hβ g
    obtain ⟨p, k, hk, hpk⟩ := GlobalTheory.T.graph_element_iwasawa_split_place F E σ h n J hJ L v hSD ⟨τ⟩ g
    have hlat := unitaryLocalPoint_latticeGraphNorm_identity F E σ h n J hJ L v g p k hk hpk
    have hgr : graphHgt σ J L v g = absEv F E v (Matrix.GeneralLinearGroup.det
        (leviOf finSumFinEquiv (matHom (Fv F v) σ (dblGram finSumFinEquiv J)) p)) := by
      rw [graphHgt, hpk, hgtFin_mul p hk]
      rfl
    refine ⟨exists_isElemDiv _, ?_, ?_⟩
    · intro d hd
      rw [hgr]
      exact GlobalTheory.T.doublingNorm_det_splitPlace_lattice_intersection F E σ h n J hJ L v hSD τ β hβ g _ hlat d hd
    · obtain ⟨d, hd⟩ := exists_isElemDiv (splitEquivIn h hJ τ β g)
      rw [hgr, GlobalTheory.T.doublingNorm_det_splitPlace_lattice_intersection F E σ h n J hJ L v hSD τ β hβ g _ hlat d hd]
      exact Finset.prod_le_one₀ (fun _ _ => by positivity) (fun i _ => min_self_inv_le_one _)
  · intro P hP g
    obtain ⟨p, k, hk, hpk⟩ := GlobalTheory.T.graph_element_iwasawa_inert_place F E σ h n J hJ L v hSD P hP g
    have hlat := unitaryLocalPoint_latticeGraphNorm_identity F E σ h n J hJ L v g p k hk hpk
    have hgr : graphHgt σ J L v g = absEv F E v (Matrix.GeneralLinearGroup.det
        (leviOf finSumFinEquiv (matHom (Fv F v) σ (dblGram finSumFinEquiv J)) p)) := by
      rw [graphHgt, hpk, hgtFin_mul p hk]
      rfl
    obtain ⟨l, hl1, hl2⟩ := GlobalTheory.T.doublingNorm_det_inertPlace_lattice_length F E σ h n J hJ L v P hP g _ hlat
    refine ⟨⟨l, hl1, hgr.trans hl2⟩, ?_⟩
    rw [hgr, hl2]
    apply natCast_zpow_neg_le_one
    exact Nat.one_le_iff_ne_zero.mpr (fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0))

end GlobalTheory.GraphNorm

end
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.galois_representation_of_eigensystem : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ {E : Type} [NormedField E] [IsAlgClosed E] [Algebra ℤ_[l] E], (∀ z : ℤ_[l], ‖algebraMap ℤ_[l] E z‖ = ‖z‖) → ∀ (lam : Letter → E), X.SSBB N l w E lam → ∀ (ρ : (Ω ≃ₐ[ℚ] Ω) →* GL (Fin 2) E) (S0 : Finset ℕ), (∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖(fun s => Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E)) (s * s') - (fun s => Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E)) (s)‖ < δ) → (∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖(fun s => Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E)) (s * s') - (fun s => Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E)) (s)‖ < δ) → (∀ q : ℕ, q.Prime → q ∉ S0 → ∀ s, FrobAt q s → Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E) = lam (Letter.T q) ∧ Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E) = (q : E) ^ (w + 1) * lam (Letter.D q)) → (∀ V : Submodule E (Fin 2 → E), (∀ s v, v ∈ V → (ρ s : Matrix (Fin 2) (Fin 2) E) *ᵥ v ∈ V) → V = ⊥ ∨ V = ⊤) → ∃ (m : ℕ) (π : Fin m → (E ⊗[ℤ_[l]] X.Fn l) →ₗ[E] (Fin 2 → E)) (σ : Fin m → (Fin 2 → E) →ₗ[E] (E ⊗[ℤ_[l]] X.Fn l)) (P : FreeAlgebra E Letter), P ∈ admissibleLettersSubalgebra E N l ∧ FreeAlgebra.lift E lam P = 1 ∧ (∀ x ∈ X.VB N l w E, (∀ T : Letter, admitted N l T → X.opV N l E T x = lam T • x) → ∑ i, σ i (π i x) = x) ∧ (∀ i v, σ i v ∈ X.VB N l w E) ∧ (∀ i s, ∀ x ∈ X.VB N l w E, π i (X.galV l E s x) = (ρ s : Matrix (Fin 2) (Fin 2) E) *ᵥ π i x) ∧ (∀ i s v, X.galV l E s (σ i v) = σ i ((ρ s : Matrix (Fin 2) (Fin 2) E) *ᵥ v)) ∧ (∀ i (T : Letter) v, admitted N l T → X.opV N l E T (σ i v) = lam T • σ i v) ∧ (∀ i (T : Letter), admitted N l T → ∀ x ∈ X.VB N l w E, π i (X.opV N l E T x) = lam T • π i x) ∧ (∀ i j v, π i (σ j v) = if i = j then v else 0) ∧ ∀ x ∈ X.VB N l w E, FreeAlgebra.lift E (X.opV N l E) P x = ∑ i, σ i (π i x) := by
  first | (exact @GlobalTheory.KZ.HeckeProj.heckeProj_main) | (exact GlobalTheory.KZ.HeckeProj.heckeProj_main) | (intros; apply GlobalTheory.KZ.HeckeProj.heckeProj_main  <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AutMult

theorem topologicalClosure_span_eq_top_of_le {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (U : Submodule ℂ K) (s : Set U)
    (h : U ≤ (Submodule.span ℂ (Subtype.val '' s)).topologicalClosure) :
    (Submodule.span ℂ s).topologicalClosure = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨v, hv⟩ -
  have hmap : (Subtype.val '' (Submodule.span ℂ s : Set U) : Set K) = Submodule.span ℂ (Subtype.val '' s) := by
    exact congrArg (fun p : Submodule ℂ K => (p : Set K)) (Submodule.map_span U.subtype s)
  have h2 : v ∈ closure (Subtype.val '' (Submodule.span ℂ s : Set U)) := by
    rw [hmap, ← Submodule.topologicalClosure_coe]
    exact h hv
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, Set.mem_preimage]
  exact h2

theorem exists_isIrrUnitary_isCopyFinDS : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (W : Type) [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ → mCuspDS μ σ M ≠ 0 →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (π : GA D V →* (H →L[ℂ] H)),
      IsIrrUnitary π ∧ IsCopyFinDS σ M π ⊤ := by
  intro D V S M μ _ _ W _ _ σ hirr hadm hm
  classical
  have hne : homFinDS σ M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) ≠ ⊥ := fun h => hm (by rw [mCuspDS, h]; simp)
  obtain ⟨T, hT, hT0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hinj : Function.Injective T := injective_of_mem_homInto hirr hT hT0
  have hTt : T ∈ homFinDS σ M (RG V μ) ⊤ := homTensorPi_mono le_top hT
  obtain ⟨U, hUdef⟩ : ∃ U : Submodule ℂ (DividedPowerChartLift V μ), (Submodule.span ℂ {v | ∃ w y, v = T w y}).topologicalClosure = U :=
    ⟨_, rfl⟩
  have hcopy : IsCopyFinDS σ M (RG V μ) U := ⟨T, hTt, hinj, hUdef⟩
  have hU := TrCopy.isIrredSubrep_of_isCopyFinDS D V S M W σ hirr hadm (DividedPowerChartLift V μ) (RG V μ) (isUnitaryRep_RG V μ) U hcopy
  refine ⟨U, inferInstance, inferInstance, hU.1.rep, isIrrUnitary_rep (isUnitaryRep_RG V μ) hU, ?_⟩
  have hmem : ∀ w y, T w y ∈ U := fun w y =>
    hUdef ▸ Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨w, y, rfl⟩)
  let T' : W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H U :=
    { toFun := fun w => (T w).codRestrict U (hmem w)
      map_add' := fun a b => by ext y; simp
      map_smul' := fun c a => by ext y; simp }
  have hT'v : ∀ w y, (T' w y : DividedPowerChartLift V μ) = T w y := fun _ _ => rfl
  have hTm := mem_homTensorPi.1 hTt
  refine ⟨T', mem_homTensorPi.2 ⟨fun _ _ => trivial, fun g w y => Subtype.ext ?_, fun i g w y => Subtype.ext ?_⟩,
    fun a b h => hinj (ContinuousMultilinearMap.ext fun y => congrArg Subtype.val (DFunLike.congr_fun h y)), ?_⟩
  · exact hTm.2.1 g w y
  · exact hTm.2.2 i g w y
  · have himg : Subtype.val '' {v : U | ∃ w y, v = T' w y} = {v | ∃ w y, v = T w y} := by
      ext x
      constructor
      · rintro ⟨_, ⟨w, y, rfl⟩, rfl⟩
        exact ⟨w, y, rfl⟩
      · rintro ⟨w, y, rfl⟩
        exact ⟨T' w y, ⟨w, y, rfl⟩, rfl⟩
    exact topologicalClosure_span_eq_top_of_le U _ (le_of_eq (by rw [himg]; exact hUdef.symm))

end GlobalTheory.AutMult
end
end
