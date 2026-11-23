module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Mathlib.RingTheory.PiTensorProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1435
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1703
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1477
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinpolyDefinitePairsTermNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1705
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1706
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1673
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
import Mathlib.Data.Nat.Choose.Multinomial
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682

@[expose] public section

section

noncomputable section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD GlobalTheory.VacLn

namespace GlobalTheory.HoweD

theorem vacD_ne_zero {ι : Type} [Fintype ι] {P Q R S : ι → ℕ} :
    (PiTensorProduct.tprod ℂ fun w : ι => (1 : Pol (P w) (Q w) (R w) (S w))) ≠ 0 := by
  intro h
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap
    fun w => (MvPolynomial.aeval (R := ℂ) (S₁ := ℂ) (σ := Ln (P w) (Q w) (R w) (S w)) fun _ => 0).toLinearMap)) h
  simp at this

theorem vacLineD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → IsStd ψ →
    FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ → ∀ (f₀ : SInf F κ) (ε : InfinitePlace F → ℤˣ),
    (∀ u u' : Matrix α β (AE F E), At (evI F) u → At (evI F) u' → ∀ c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ,
      (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
      (∀ w, u'.map (piInf (τ w)) = A w * ((((ε w : ℤ) : ℂ) * Complex.I) • (Jm (P w) (Q w) * c w * Jm (R w) (S w))) * (C w)ᵀ) →
      ∀ f f' : SInf F κ, SD (fun t => d.rho ψ (realAd F t • u)) f₀ f → SD (fun t => d.rho ψ (realAd F t • u')) f₀ f' →
        f' = Complex.I • f) →
    ∃ z : ℂ, f₀ = z • Φ (PiTensorProduct.tprod ℂ fun _ => 1) := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ hCM hStd hFr hΦ f₀ ε hyp
  have hD : DerEx := GlobalTheory.T.archHeisenbergDerivatives_exist
  obtain ⟨D, hDu⟩ := hD F E σ α β κ ψ JA JB d hStd
  obtain ⟨J, e, e', hJ, he, hJe, he1, he2, hy⟩ := GlobalTheory.T.exists_archimedeanPhaseSpace_complexStructure_signatures F E σ α β κ P Q R S τ JA JB d a b A C ε hCM hFr
  have hDx : ∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x = fderiv ℝ f x (coord d u).1 -
      2 * Real.pi * Complex.I * (trPair F κ x (coord d u).2 : ℝ) * f x := fun u hu f x => (hDu u hu f).2 x
  have hf : ∀ y x, fderiv ℝ f₀ x (J (y - (2 : ℝ) • e y)).1 - 2 * Real.pi * Complex.I *
      (trPair F κ x (J (y - (2 : ℝ) • e y)).2 : ℝ) * f₀ x =
      Complex.I * (fderiv ℝ f₀ x y.1 - 2 * Real.pi * Complex.I * (trPair F κ x y.2 : ℝ) * f₀ x) := by
    intro y x
    obtain ⟨u, u', u₁, c, hu, hu', -, hc, hc', -, h0, h', -⟩ := hy y
    have key := hyp u u' hu hu' c hc hc' (D u f₀) (D u' f₀) (hDu u hu f₀).1 (hDu u' hu' f₀).1
    have := congrArg (fun g : SInf F κ => g x) key
    simp only [SchwartzMap.smul_apply, smul_eq_mul] at this
    rw [hDx u hu, hDx u' hu', h0, h'] at this
    exact this
  set g₀ := Φ (PiTensorProduct.tprod ℂ fun _ => 1) with hg₀
  have hg0 : g₀ ≠ 0 := fun h => vacD_ne_zero (hΦ.1 (h.trans (map_zero Φ).symm))
  have hg : ∀ y x, fderiv ℝ g₀ x (J y).1 - 2 * Real.pi * Complex.I * (trPair F κ x (J y).2 : ℝ) * g₀ x =
      Complex.I * (fderiv ℝ g₀ x y.1 - 2 * Real.pi * Complex.I * (trPair F κ x y.2 : ℝ) * g₀ x) := by
    intro y x
    obtain ⟨u, -, u₁, c, hu, -, hu₁, hc, -, hc₁, h0, -, h1⟩ := hy y
    have e0 := GlobalTheory.T.hasArchDerivativeOnPureTensor_unique_adelicOperators (hDu u hu g₀).1 (hΦ.2 u hu c hc _)
    have e1 := GlobalTheory.T.hasArchDerivativeOnPureTensor_unique_adelicOperators (hDu u₁ hu₁ g₀).1 (hΦ.2 u₁ hu₁ _ hc₁ _)
    rw [GlobalTheory.T.fock_vacuum_pi_tensor_heisenberg_factorwise_signature, map_smul, ← e0] at e1
    have := congrArg (fun g : SInf F κ => g x) e1
    simp only [SchwartzMap.smul_apply, smul_eq_mul] at this
    rw [hDx u hu, hDx u₁ hu₁, h0, h1] at this
    exact this
  obtain ⟨z, hz⟩ := GlobalTheory.T.schwartz_complexStructure_vacuum_solution_eq_smul (trPair F κ) (fun y h => GlobalTheory.T.archimedeanTracePairingBilinear_nondegenerate y h) J e e' hJ he hJe he1 he2 f₀ g₀ hg0 hg hf
  exact ⟨z, hz⟩

end GlobalTheory.HoweD

end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.finite_minpoly_definitePairs_term_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
    ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      {P0 : Polynomial G.F | ∃ P : GlobalTheory.LKDef.DPair G, P.pol = P0 ∧ Irreducible P.pol ∧
        P.term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite := by
  first | exact @GlobalTheory.LKDef.FinPol.finite_pol_term_ne_zero | exact GlobalTheory.LKDef.FinPol.finite_pol_term_ne_zero | (intros; apply GlobalTheory.LKDef.FinPol.finite_pol_term_ne_zero <;> assumption)
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem hx_of_isONFr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r g n : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → Even n → ∀ x : Frame X.Ψ r, IsONFr X x → x ∈ X.dom ∧ IsUnitFr X x ∧ ∀ z w : Fin g → ℂ, hx X bas idx x z w = ∑ j, (X.c (idx j).1 : ℂ) * z j * conj (w j) := by
  intro E _ _ _ r g n X bas idx hs _ x ho
  have hsg : ∀ a : ℕ, FD.sgn X.p0 a = 1 ∨ FD.sgn X.p0 a = -1 := fun a => by
    unfold FD.sgn; split_ifs <;> simp
  have e (τ : X.Ψ) (i : Fin (r + 1)) : dmin X.Gm x τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    unfold dmin lminor
    rw [ho τ, sgnM, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    unfold psgn
    push_cast
    exact Fin.prod_univ_eq_prod_range (fun a => ((FD.sgn X.p0 a : ℝ) : ℂ)) (i : ℕ)
  have h0 (i : ℕ) : psgn X.p0 i ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun a _ => by rcases hsg a with h | h <;> rw [h] <;> norm_num
  have hd : x ∈ X.dom := by
    refine fun τ => ⟨fun h => ?_, fun i => ?_⟩
    · have h1 : FD.gram τ.1 X.Gm (mat x τ) =
          (mat x τ)ᵀ * X.Gm.map τ.1 * (mat x τ).map (starRingEnd ℂ) := by
        ext a b
        simp only [FD.gram, hermC, FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
          Matrix.map_apply, Finset.sum_mul]
        exact Finset.sum_comm
      have h2 := congrArg Matrix.det (h1.symm.trans (ho τ))
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h, zero_mul, zero_mul, sgnM,
        Matrix.det_diagonal] at h2
      refine Finset.prod_ne_zero_iff.2 (fun a _ => ?_) h2.symm
      rcases hsg a with h | h <;> rw [h] <;> norm_num
    · rw [e, Complex.ofReal_re]
      exact mul_self_pos.2 (h0 _)
  refine ⟨hd, fun τ i => ?_, (GlobalTheory.Dict.hx_ortho E r X g bas idx hs x hd ho).1⟩
  rw [e, psgn]
  push_cast
  rw [norm_prod]
  exact Finset.prod_eq_one fun a _ => by rcases hsg a with h | h <;> rw [h] <;> simp

end GlobalTheory.AdTh
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_finiteIndex_levi_subgroup_unipotentConj_integral : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)), ∃ U : Subgroup (GLw a w × GLw b w), U ≤ (GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)) ∧ U.relIndex ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) ≠ 0 ∧ ∀ k ∈ U, (blk h w 1 X)⁻¹ * blk h w k 0 * blk h w 1 X ∈ GlobalTheory.LFun.KGL w (n := n) := by
  first | exact @GlobalTheory.LeviDesc.ConjStab.exists_stab | exact GlobalTheory.LeviDesc.ConjStab.exists_stab | (intros; apply GlobalTheory.LeviDesc.ConjStab.exists_stab <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.normalisedMatrixIntegral_comp_linearEquiv_det : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (a b : ℕ) (L : Matrix (Fin a) (Fin b) (w.adicCompletion E) →ₗ[w.adicCompletion E] Matrix (Fin a) (Fin b) (w.adicCompletion E)) (φ : Matrix (Fin a) (Fin b) (w.adicCompletion E) → ℂ), LinearMap.det L ≠ 0 → (∃ U : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (U : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ ∀ x, ∀ y ∈ U, φ (x + y) = φ x) → HasCompactSupport φ → hint (intMat a b w) (fun X => φ (L (Multiplicative.toAdd X))) = (absHalf w (LinearMap.det L) ^ 2)⁻¹ * hint (intMat a b w) (fun X => φ (Multiplicative.toAdd X)) := by
  first | exact @GlobalTheory.LeviDesc.hint_comp_linear | exact GlobalTheory.LeviDesc.hint_comp_linear | (intros; apply GlobalTheory.LeviDesc.hint_comp_linear <;> assumption)
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.psi_halfSymplectic_orthonormalFrame : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ x : Frame X.Ψ r, IsONFr X x → ∀ v w : WO V W, v.map (finPart D) = 0 → ψ (symplOH V W v w) = cexp (Real.pi * I * ((∑ b, (hx X bas idx x (zOf θ V W hr X idx x v b) (zOf θ V W hr X idx x w b)).im : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.AdThSympl.psi_symplOH_eq_of_isONFr | exact GlobalTheory.AdThSympl.psi_symplOH_eq_of_isONFr | (intros; apply GlobalTheory.AdThSympl.psi_symplOH_eq_of_isONFr <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.finite_productOfLocalFunctionsUnitary_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → {q : finU (E := E) (n := n) ⧸ globLev S K' | globFn S f q.out ≠ 0}.Finite := by
  first | exact @GlobalTheory.BCT.finite_globFn_ne_zero | exact GlobalTheory.BCT.finite_globFn_ne_zero | (intros; apply GlobalTheory.BCT.finite_globFn_ne_zero <;> assumption)
end

section

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

theorem _root_.GlobalTheory.T.del_dbar_leibniz_evenForm_mul : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (w : A.Pt → Ev n) (β : A.Fld),
    A.IsForm (GlobalTheory.LineForm.fld A w) → A.IsForm β →
    A.del (GlobalTheory.LineForm.fld A w * β) = A.del (GlobalTheory.LineForm.fld A w) * β + GlobalTheory.LineForm.fld A w * A.del β ∧
    A.dbar (GlobalTheory.LineForm.fld A w * β) = A.dbar (GlobalTheory.LineForm.fld A w) * β + GlobalTheory.LineForm.fld A w * A.dbar β := by
  first | exact @GlobalTheory.CxForm.HolAtlas.del_dbar_even_mul | exact GlobalTheory.CxForm.HolAtlas.del_dbar_even_mul | (intros; apply GlobalTheory.CxForm.HolAtlas.del_dbar_even_mul <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.orbitalIntegral_semidirectProduct_unfolding : ∀ (P M N : Type) [Group P] [Group M] [Group N] [TopologicalSpace P] [TopologicalSpace M] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ γ : M, (∀ p, p ∈ twCent (MonoidHom.id P) (s γ) ↔ ∃ t ∈ twCent (MonoidHom.id M) γ, s t = p) → (∀ p, p ∈ cptPart (twCent (MonoidHom.id P) (s γ)) ↔ ∃ t ∈ cptPart (twCent (MonoidHom.id M) γ), s t = p) → (∀ q : M, twCent (MonoidHom.id M) γ ⊓ KM.map (MulAut.conj q).toMonoidHom ≤ cptPart (twCent (MonoidHom.id M) γ)) → (∀ X : N, ∃ U : Subgroup M, U ≤ KM ∧ U.relIndex KM ≠ 0 ∧ ∀ k ∈ U, (u X)⁻¹ * s k * u X ∈ KP) → ∀ F : P → ℂ, (∀ k ∈ KP, ∀ x, F (k⁻¹ * x * k) = F x) → {d : DoubleCoset.Quotient (twCent (MonoidHom.id P) (s γ) : Set P) (KP : Set P) | F ((Quotient.out d)⁻¹ * s γ * Quotient.out d) ≠ 0}.Finite → twOrb (MonoidHom.id P) KP (s γ) F = twOrb (MonoidHom.id M) KM γ (fun m' => hint L (fun X => F ((u X)⁻¹ * s m' * u X))) := by
  first | exact @GlobalTheory.Unfold.twOrb_unfold | exact GlobalTheory.Unfold.twOrb_unfold | (intros; apply GlobalTheory.Unfold.twOrb_unfold <;> assumption)
end

section

noncomputable section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.LocGlue

theorem entry_mem {E : Type} [Field E] [NumberField E] {n : ℕ} {v : HeightOneSpectrum (𝓞 E)}
    {g : GL (Fin n) (v.adicCompletion E)} (hg : g ∈ GlobalTheory.LFun.KGL v (n := n)) (i j : Fin n) :
    g.val i j ∈ v.adicCompletionIntegers E ∧ (g⁻¹ : GL (Fin n) (v.adicCompletion E)).val i j ∈ v.adicCompletionIntegers E := by
  obtain ⟨g0, rfl⟩ := hg
  refine ⟨(g0.val i j).2, ?_⟩
  rw [← map_inv]
  exact ((g0⁻¹).val i j).2

theorem glue : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (g : ∀ v : HeightOneSpectrum (𝓞 E), GL (Fin n) (v.adicCompletion E)), (∀ᶠ v in cofinite, g v ∈ GlobalTheory.LFun.KGL v (n := n)) → ∃ k : GL (Fin n) (Af E), ∀ v, GeneralLinearGroup.map (pLoc E v) k = g v := by
  intro E _ _ n g hg
  have hent : ∀ i j, ∀ᶠ v in cofinite, (g v).val i j ∈ v.adicCompletionIntegers E ∧
      ((g v)⁻¹ : GL (Fin n) (v.adicCompletion E)).val i j ∈ v.adicCompletionIntegers E :=
    fun i j => hg.mono fun v hv => entry_mem hv i j
  let M : Matrix (Fin n) (Fin n) (Af E) := fun i j => ⟨fun v => (g v).val i j, (hent i j).mono fun v h => h.1⟩
  let N : Matrix (Fin n) (Fin n) (Af E) := fun i j =>
    ⟨fun v => ((g v)⁻¹ : GL (Fin n) (v.adicCompletion E)).val i j, (hent i j).mono fun v h => h.2⟩
  have hM : ∀ v, RingHom.mapMatrix (pLoc E v) M = (g v).val := fun v => rfl
  have hN : ∀ v, RingHom.mapMatrix (pLoc E v) N = ((g v)⁻¹ : GL (Fin n) (v.adicCompletion E)).val := fun v => rfl
  have hMN : M * N = 1 := GlobalTheory.SplitPts.matAf_ext fun v => by
    rw [map_mul, map_one, hM, hN, Units.mul_inv]
  have hNM : N * M = 1 := GlobalTheory.SplitPts.matAf_ext fun v => by
    rw [map_mul, map_one, hM, hN, Units.inv_mul]
  exact ⟨⟨M, N, hMN, hNM⟩, fun v => Units.ext (hM v)⟩

theorem intst : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (v u : HeightOneSpectrum (𝓞 E)) (f : v.adicCompletion E →+* u.adicCompletion E), (∀ x, Valued.v (f x) = Valued.v x) → ∀ g ∈ GlobalTheory.LFun.KGL v (n := n), invT n _ (GeneralLinearGroup.map f g) ∈ GlobalTheory.LFun.KGL u (n := n) := by
  intro E _ _ n v u f hf g hg
  obtain ⟨g0, rfl⟩ := hg
  let r : Formalism.UG.Ov E v →+* Formalism.UG.Ov E u := f.restrict _ _ fun x hx => by
    change _ ∈ u.adicCompletionIntegers E
    change x ∈ v.adicCompletionIntegers E at hx
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx ⊢
    rw [hf]
    exact hx
  refine ⟨invT n _ (GeneralLinearGroup.map r g0), ?_⟩
  apply Units.ext
  ext i j
  rfl

theorem ns : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (Y : ∀ v : HeightOneSpectrum (𝓞 E), GL (Fin n) (v.adicCompletion E)) (u : HeightOneSpectrum (𝓞 E)), ¬ IsSplitAt u → GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) u) (Y (conjSrc (GlobalTheory.SplitPts.conjE E) u)) = GeneralLinearGroup.map (cj u) (Y u) := by
  intro E _ _ _ n Y u hu
  have key : ∀ (v : HeightOneSpectrum (𝓞 E)) (_ : v = u) (f : v.adicCompletion E →+* u.adicCompletion E), Continuous f →
      (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (IsCMField.complexConj E k)) →
      GeneralLinearGroup.map f (Y v) = GeneralLinearGroup.map (cj u) (Y u) := by
    rintro v rfl f hf hext
    have hex : ∃ s : v.adicCompletion E →+* v.adicCompletion E, Continuous s ∧
        ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := ⟨f, hf, hext⟩
    have hcj : cj v = hex.choose := by unfold cj; rw [dite_eq_left hex]
    have hfs : (f : v.adicCompletion E → v.adicCompletion E) = hex.choose :=
      (HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf hex.choose_spec.1
        (funext fun k => (hext k).trans (hex.choose_spec.2 k).symm)
    rw [hcj]
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact congrFun hfs ((Y v).val i j)
  have hcu : conjSrc (GlobalTheory.SplitPts.conjE E) u = u := by
    by_contra h
    exact hu ⟨_, h, (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) u _).2
      (Or.inr (GlobalTheory.SplitPts.conjPl_self_conjSrc u))⟩
  exact key _ hcu _ (conjLoc_spec _ u).1 (conjLoc_spec _ u).2.1

theorem twice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (Y : ∀ v : HeightOneSpectrum (𝓞 E), GL (Fin n) (v.adicCompletion E)) (u : HeightOneSpectrum (𝓞 E)), GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) u) (GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) (conjSrc (GlobalTheory.SplitPts.conjE E) u)) (Y (conjSrc (GlobalTheory.SplitPts.conjE E) (conjSrc (GlobalTheory.SplitPts.conjE E) u)))) = Y u := by
  intro E _ _ _ n Y u
  have key : ∀ (v : HeightOneSpectrum (𝓞 E)) (_ : v = u) (f : v.adicCompletion E →+* u.adicCompletion E), Continuous f →
      (∀ k : E, f (algebraMap E _ k) = algebraMap E _ k) → GeneralLinearGroup.map f (Y v) = Y u := by
    rintro v rfl f hf hext
    have hfs : (f : v.adicCompletion E → v.adicCompletion E) = id :=
      (HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf continuous_id (funext fun k => hext k)
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact congrFun hfs ((Y v).val i j)
  have h := key _ (GlobalTheory.SplitPts.conjSrc_conjSrc_cm u)
    ((conjLoc (GlobalTheory.SplitPts.conjE E) u).comp (conjLoc (GlobalTheory.SplitPts.conjE E) (conjSrc (GlobalTheory.SplitPts.conjE E) u)))
    ((conjLoc_spec _ u).1.comp (conjLoc_spec _ _).1) fun k => by
      rw [RingHom.comp_apply, (conjLoc_spec _ _).2.1, (conjLoc_spec _ _).2.1]
      exact congrArg _ (IsCMField.complexConj_apply_apply E k)
  rw [← h]
  rfl

end GlobalTheory.BCT.LocGlue

theorem GlobalTheory.BCT.exists_finU_of_loc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ S : Set (Pl E), IsSection S → ∀ y : ∀ w : Pl E, UL n w, (∀ᶠ w in cofinite, y w ∈ KL n w) → ∃ x : finU (E := E) (n := n), ∀ w ∈ S, toSub (UL n w) (cLoc w (x : UA E n)) = y w := by
  intro E _ _ _ _ n S hS y hy
  set c := GlobalTheory.SplitPts.conjE E with hc
  have hnotS : ∀ v, v ∉ S → conjSrc c v ∈ S := by
    intro v hv
    obtain ⟨s, ⟨hsS, hsv⟩, -⟩ := hS v
    have hne : v ≠ s := fun e => hv (e ▸ hsS)
    have hsp : IsSplitAt s := ⟨v, hne, hsv.symm⟩
    obtain ⟨-, -, hover⟩ := GlobalTheory.SplitPts.over_split hsp
    rcases hover v hsv.symm with h | h
    · exact absurd h hne
    · rw [h, GlobalTheory.SplitPts.conjSrc_conjSrc_cm]; exact hsS
  have hSsplit : ∀ v ∈ S, IsSplitAt v → conjSrc c v ∉ S := by
    intro v hv hsp h
    obtain ⟨hne, hund, -⟩ := GlobalTheory.SplitPts.over_split hsp
    exact hne ((hS v).unique ⟨h, hund⟩ ⟨hv, rfl⟩)
  let z : ∀ v : Pl E, GLw n v := fun v => if v ∈ S then (y v).1 else
    invT n _ (GeneralLinearGroup.map (conjLoc c v) (y (conjSrc c v)).1)
  have hz_in : ∀ v ∈ S, z v = (y v).1 := fun v hv => if_pos hv
  have hz_out : ∀ v, v ∉ S → z v = invT n _ (GeneralLinearGroup.map (conjLoc c v) (y (conjSrc c v)).1) :=
    fun v hv => if_neg hv
  have hint : ∀ᶠ v in cofinite, z v ∈ GlobalTheory.LFun.KGL v (n := n) := by
    have h1 : ∀ᶠ v in cofinite, (y v).1 ∈ GlobalTheory.LFun.KGL v (n := n) := hy.mono fun v hv => Subgroup.mem_subgroupOf.1 hv
    have h2 := (conjSrc_injective c).tendsto_cofinite.eventually h1
    filter_upwards [h1, h2] with v a1 a2
    by_cases hv : v ∈ S
    · rw [hz_in v hv]; exact a1
    · rw [hz_out v hv]; exact GlobalTheory.BCT.LocGlue.intst E n _ v (conjLoc c v) (conjLoc_spec c v).2.2 _ a2
  obtain ⟨k, hk⟩ := GlobalTheory.BCT.LocGlue.glue E n z hint
  have hk' : ∀ u, ((GeneralLinearGroup.map (pLoc E (conjSrc c u)) k).val.map (conjLoc c u))ᵀ *
      (GeneralLinearGroup.map (pLoc E u) k).val = 1 := by
    intro u
    rw [hk, hk]
    show ((GeneralLinearGroup.map (conjLoc c u) (z (conjSrc c u))).val)ᵀ * (z u).val = 1
    by_cases hu : u ∈ S
    · by_cases hsp : IsSplitAt u
      · rw [hz_out _ (hSsplit u hu hsp), hz_in u hu, GlobalTheory.SplitPts.invT_map,
          GlobalTheory.BCT.LocGlue.twice E n (fun v => (y v).1) u]
        change ((((y u).1)⁻¹ : GLw n u).val)ᵀᵀ * (y u).1.val = 1
        rw [Matrix.transpose_transpose, Units.inv_mul]
      · have hcu : conjSrc c u = u := by
          by_contra h
          exact hsp ⟨_, h, (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
            (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) u _).2
            (Or.inr (GlobalTheory.SplitPts.conjPl_self_conjSrc u))⟩
        rw [hz_in _ (by rw [hcu]; exact hu), hz_in u hu, GlobalTheory.BCT.LocGlue.ns E n (fun v => (y v).1) u hsp]
        have key : ∀ g : GLw n u, g ∈ UL n u → g ∈ UJ (cj u) 1 := by
          intro g hg
          unfold UL at hg
          rwa [if_neg hsp] at hg
        have hUL : (y u).1 ∈ UJ (cj u) 1 := key _ (y u).2
        have h3 : cT (cj u) (y u).1.val * 1 * (y u).1.val = 1 := hUL
        rw [Matrix.mul_one] at h3
        exact h3
    · rw [hz_out u hu, hz_in _ (hnotS u hu)]
      change ((GeneralLinearGroup.map (conjLoc c u) (y (conjSrc c u)).1).val)ᵀ *
        (((GeneralLinearGroup.map (conjLoc c u) (y (conjSrc c u)).1)⁻¹ : GLw n u).val)ᵀ = 1
      rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  let x : finU (E := E) (n := n) := ⟨⟨finGL E n k, GlobalTheory.SplitPts.finGL_mem_UA k hk'⟩, MonoidHom.mem_ker.2 (pInf_finGL k)⟩
  refine ⟨x, fun w hw => ?_⟩
  show toSub (UL n w) (cLoc w ⟨finGL E n k, GlobalTheory.SplitPts.finGL_mem_UA k hk'⟩) = y w
  rw [GlobalTheory.SplitPts.cLoc_finGL, hk, hz_in w hw]
  unfold toSub
  rw [dite_eq_left (y w).2]
end
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSCore

theorem choose_mul_interNum_le_hdim : ∀ (k : Type) [Field k] [Infinite k] (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (GlobalTheory.strHom k (X := Y)) → ∀ (L : LB Y) (hL : L.IsLB) (N : ℕ) (b : Fin N → L.Sec), (∀ y : Y, ∃ i, y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (b i)) → ∀ (d : ℕ) (F : Y.Modules) [IsFiniteQC F], suppDim F ≤ d → ∀ (j₀ : ℤ), VanishFrom L F j₀ → ∀ m : ℕ, (m.choose d : ℤ) * GlobalTheory.interNum k F (fun _ : Fin d => L) ≤ GlobalTheory.hdim k (GlobalTheory.twistZ F L (j₀ + m)) 0 := by
  intro k _ _ Y _ hY L hL N b hb d
  have hNo : AlgebraicGeometry.IsNoetherian Y := isNoetherian_of_isProjOver hY
  have hb' : ⨆ i, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (b i) = ⊤ :=
    top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 (hb y)
  have hf := algebraMap_eq_strHom k Y
  induction d with
  | zero =>
    intro F _ hF j₀ _ m
    rw [interNum_of_isEmpty, GlobalTheory.T.zero_dim_support_euler_char k Y hY L hL F (by simpa using hF)]
    simp
  | succ d ih =>
    intro F _ hF j₀ hV m
    obtain ⟨c, hc⟩ := exists_sum_mono_cutHom (k := k) F hL b hb'
    set t : L.Sec := ∑ i, algebraMap k Γ(Y, ⊤) (c i) • b i
    obtain ⟨hV', hr⟩ := GlobalTheory.T.hyperplane_section_vanishing_shift k Y hY L hL F t j₀ hV
    have hI : GlobalTheory.interNum k F (fun _ : Fin (d + 1) => L) =
        GlobalTheory.interNum k (GlobalTheory.cut F hL t) (fun _ : Fin d => L) := by
      rw [← interNum_cons_eq_interNum_cut hL t (P := fun _ : Fin d => L) (fun _ => hL)
        (finiteCohTwists_of_isProjOver hf F hY)]
      congr 1
      funext i
      refine Fin.cases rfl (fun _ => rfl) i
    have ih' := ih (GlobalTheory.cut F hL t) (suppDim_cut_le F hL t hF) (j₀ + 1) hV'
    rw [hI]
    induction m with
    | zero => simp
    | succ m ihm =>
      have h1 := hr (j₀ + 1 + m) (by omega)
      have h2 := ih' m
      have e1 : j₀ + ((m + 1 : ℕ) : ℤ) = j₀ + 1 + m := by push_cast; ring
      have e2 : j₀ + 1 + (m : ℤ) - 1 = j₀ + m := by ring
      rw [e2] at h1
      rw [e1, h1, Nat.choose_succ_succ']
      push_cast
      linarith

end GlobalTheory.HSCore
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.curvature_power_pullback_holomorphic : ∀ (n n' : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (φ : V n' → V n) (w : V n'), ContDiffAt ℂ 2 φ w → MContDiffAt ∞ G (φ w) → IsUnit (G (φ w)).det → (∀ k l i j, ∀ G' : V n → Matrix r r ℂ, MContDiffAt ∞ G' (φ w) → IsUnit (G' (φ w)).det → ((curvEv (fun x => G (φ x)) w ^ k * curvEv (fun x => G' (φ x)) w ^ l) i j : Alt n') = pull (fderiv ℂ φ w) ((curvEv G (φ w) ^ k * curvEv G' (φ w) ^ l) i j : Alt n)) ∧ ∀ k, (powAt (fun x => G (φ x)) w k : Alt n') = pull (fderiv ℂ φ w) (powAt G (φ w) k) ∧ (chernAt (fun x => G (φ x)) w k : Alt n') = pull (fderiv ℂ φ w) (chernAt G (φ w) k) := by
  first | exact @GlobalTheory.ChernCalc.curv_pow_chern_comp_holo | exact GlobalTheory.ChernCalc.curv_pow_chern_comp_holo | (intros; apply GlobalTheory.ChernCalc.curv_pow_chern_comp_holo <;> assumption)
end
