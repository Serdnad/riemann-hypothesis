module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle277
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle140
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle304
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle164
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle166
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle332
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle009
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle358
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle340
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle182
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle339
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle172
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactTorusActsFockVectorRowHighest
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.EmbHeight

open scoped NNReal
open GlobalTheory.AdelicU Formalism.UG

section Generic

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

theorem htOf_le_mul {R : Type} [CommRing R] {N : Matrix n n R → ℝ≥0} {N₁ : Matrix m m R → ℝ≥0} {c : ℝ≥0}
    (hc : 1 ≤ c) (X : GL n R) (x : GL m R) (h1 : N (X : Matrix n n R) ≤ c * max 1 (N₁ (x : Matrix m m R)))
    (h2 : N ((X⁻¹ : GL n R) : Matrix n n R) ≤ c * max 1 (N₁ ((x⁻¹ : GL m R) : Matrix m m R))) :
    htOf N X ≤ c * htOf N₁ x := by
  refine max_le (one_le_mul_of_one_le_of_one_le hc (one_le_htOf _ _)) (max_le ?_ ?_)
  · exact h1.trans (mul_le_mul' le_rfl (max_le (one_le_htOf _ _) (le_htOf _ _)))
  · exact h2.trans (mul_le_mul' le_rfl (max_le (one_le_htOf _ _) (inv_le_htOf _ _)))

theorem bc_val_aff {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (A : Matrix n n R) (B : Matrix n m R)
    (C : Matrix m n R) {X : GL n R} {x : GL m R} (h : (X : Matrix n n R) = A + B * (x : Matrix m m R) * C) :
    ((bc φ X : GL n R') : Matrix n n R') = A.map φ + B.map φ * ((bc φ x : GL m R') : Matrix m m R') * C.map φ := by
  show (X : Matrix n n R).map φ = A.map φ + B.map φ * (x : Matrix m m R).map φ * C.map φ
  rw [h, Matrix.map_add _ (map_add φ), Matrix.map_mul, Matrix.map_mul]

theorem bc_inv_aff {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (A : Matrix n n R) (B : Matrix n m R)
    (C : Matrix m n R) {X : GL n R} {x : GL m R}
    (h : ((X⁻¹ : GL n R) : Matrix n n R) = A + B * ((x⁻¹ : GL m R) : Matrix m m R) * C) :
    (((bc φ X)⁻¹ : GL n R') : Matrix n n R') =
      A.map φ + B.map φ * (((bc φ x)⁻¹ : GL m R') : Matrix m m R') * C.map φ := by
  simp only [← map_inv]
  exact bc_val_aff φ A B C h

theorem map_aff {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (A : Matrix n n R) (B : Matrix n m R)
    (C : Matrix m n R) (y : Matrix m m R) : (A + B * y * C).map φ = A.map φ + B.map φ * y.map φ * C.map φ := by
  rw [Matrix.map_add _ (map_add φ), Matrix.map_mul, Matrix.map_mul]

theorem opNorm_add_le (a b : Matrix n n ℂ) : opNorm (a + b) ≤ opNorm a + opNorm b := by
  unfold opNorm; rw [map_add (f := _)]; exact nnnorm_add_le _ _

theorem exists_opNorm_mul_mul_le (B : Matrix n m ℂ) (C : Matrix m n ℂ) :
    ∃ K : ℝ≥0, ∀ y : Matrix m m ℂ, opNorm (B * y * C) ≤ K * opNorm y := by
  let L : (EuclideanSpace ℂ m →L[ℂ] EuclideanSpace ℂ m) →ₗ[ℂ] (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :=
    { toFun := fun T => Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (B * (Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ)).symm T * C)
      map_add' := fun S T => by simp only [map_add (f := _), Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun r T => by simp only [map_smul, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  let Lc := LinearMap.toContinuousLinearMap L
  refine ⟨‖Lc‖₊, fun y => ?_⟩
  have e : opNorm (B * y * C) = ‖Lc (Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) y)‖₊ := by
    show _ = ‖L _‖₊
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, StarAlgEquiv.symm_apply_apply]
    rfl
  rw [e]
  exact Lc.le_opNNNorm _

end Generic

variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

theorem normFin_add_le (v : HeightOneSpectrum (𝓞 F)) {p q : Type} [Fintype p] [Fintype q]
    (a b : Matrix p q (Fv F v ⊗[F] E)) : normFin F v (a + b) ≤ max (normFin F v a) (normFin F v b) :=
  (normFin_le_iff F v).2 fun i j =>
    (absFin_add_le F v _ _).trans (max_le_max (absFin_le_normFin F v a i j) (absFin_le_normFin F v b i j))

theorem normFin_aff_le (v : HeightOneSpectrum (𝓞 F)) (A : Matrix n n (Fv F v ⊗[F] E)) (B : Matrix n m (Fv F v ⊗[F] E))
    (C : Matrix m n (Fv F v ⊗[F] E)) (y : Matrix m m (Fv F v ⊗[F] E)) :
    normFin F v (A + B * y * C) ≤
      max 1 (max (normFin F v A) (normFin F v B * normFin F v C)) * max 1 (normFin F v y) := by
  set M := max 1 (max (normFin F v A) (normFin F v B * normFin F v C))
  have h1 : (1 : ℝ≥0) ≤ M := le_max_left _ _
  refine (normFin_add_le F v _ _).trans (max_le ?_ ?_)
  · exact (le_max_left _ _ |>.trans (le_max_right 1 _) : normFin F v A ≤ M).trans (le_mul_of_one_le_right' (le_max_left _ _))
  · calc normFin F v (B * y * C) ≤ normFin F v B * normFin F v y * normFin F v C :=
          (normFin_mul_le F v _ _).trans (mul_le_mul' (normFin_mul_le F v _ _) le_rfl)
      _ = (normFin F v B * normFin F v C) * normFin F v y := by ring
      _ ≤ M * max 1 (normFin F v y) :=
          mul_le_mul' ((le_max_right _ _).trans (le_max_right _ _)) (le_max_right _ _)

theorem exists_normInf_aff_le (w : InfinitePlace F) (A : Matrix n n (w.Completion ⊗[F] E))
    (B : Matrix n m (w.Completion ⊗[F] E)) (C : Matrix m n (w.Completion ⊗[F] E)) :
    ∃ c : ℝ≥0, 1 ≤ c ∧ ∀ y : Matrix m m (w.Completion ⊗[F] E),
      normInf F w (A + B * y * C) ≤ c * max 1 (normInf F w y) := by
  classical
  have hK : ∀ τ : EmbOver E w, ∃ K : ℝ≥0, ∀ y : Matrix m m ℂ,
      opNorm (B.map (infEmb τ) * y * C.map (infEmb τ)) ≤ K * opNorm y := fun τ =>
    exists_opNorm_mul_mul_le _ _
  choose K hK using hK
  refine ⟨1 + ∑ τ, (opNorm (A.map (infEmb τ)) + K τ), le_self_add, fun y => (normInf_le_iff F w).2 fun τ => ?_⟩
  have hy : opNorm (y.map (infEmb τ)) ≤ max 1 (normInf F w y) :=
    ((normInf_le_iff F w).1 le_rfl τ).trans (le_max_right _ _)
  have hs : opNorm (A.map (infEmb τ)) + K τ ≤ 1 + ∑ τ, (opNorm (A.map (infEmb τ)) + K τ) :=
    (Finset.single_le_sum (f := fun τ => opNorm (A.map (infEmb τ)) + K τ) (fun _ _ => zero_le)
      (Finset.mem_univ τ)).trans le_add_self
  have e := map_aff (infEmb τ) A B C y
  rw [e]
  refine (opNorm_add_le _ _).trans ?_
  have h3 := hK τ (y.map (infEmb τ))
  refine (add_le_add le_rfl h3).trans ?_
  calc opNorm (A.map (infEmb τ)) + K τ * opNorm (y.map (infEmb τ))
      ≤ opNorm (A.map (infEmb τ)) * max 1 (normInf F w y) + K τ * max 1 (normInf F w y) :=
        add_le_add (le_mul_of_one_le_right' (le_max_left _ _)) (mul_le_mul' le_rfl hy)
    _ = (opNorm (A.map (infEmb τ)) + K τ) * max 1 (normInf F w y) := by rw [add_mul]
    _ ≤ _ := mul_le_mul' hs le_rfl

theorem eventually_normFin_rect_le_one {p q : Type} [Fintype p] [Fintype q] (y : Matrix p q (AF F ⊗[F] E)) :
    ∀ᶠ v in Filter.cofinite, normFin F v (y.map (compFin F E v)) ≤ 1 := by
  simp only [normFin_le_iff, Filter.eventually_all]
  exact fun i j => eventually_absFin_le_one F (y i j)

theorem exists_heightGL_aff_le (A : Matrix n n (AF F ⊗[F] E)) (B : Matrix n m (AF F ⊗[F] E))
    (C : Matrix m n (AF F ⊗[F] E)) :
    ∃ K : ℝ≥0, ∀ (X : GL n (AF F ⊗[F] E)) (x : GL m (AF F ⊗[F] E)),
      (X : Matrix n n (AF F ⊗[F] E)) = A + B * (x : Matrix m m (AF F ⊗[F] E)) * C →
      ((X⁻¹ : GL n (AF F ⊗[F] E)) : Matrix n n (AF F ⊗[F] E)) =
        A + B * ((x⁻¹ : GL m (AF F ⊗[F] E)) : Matrix m m (AF F ⊗[F] E)) * C →
      heightGL F X ≤ K * heightGL F x := by
  have hw := fun w : InfinitePlace F =>
    exists_normInf_aff_le F w (A.map (compInf F E w)) (B.map (compInf F E w)) (C.map (compInf F E w))
  choose cw hcw1 hcw using hw
  set cv : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => max 1 (max (normFin F v (A.map (compFin F E v)))
    (normFin F v (B.map (compFin F E v)) * normFin F v (C.map (compFin F E v)))) with hcv
  have hfin : (Function.mulSupport cv).Finite := by
    have h := ((eventually_normFin_rect_le_one F A).and (eventually_normFin_rect_le_one F B)).and
      (eventually_normFin_rect_le_one F C)
    refine (Filter.eventually_cofinite.1 h).subset fun v hv hv' => hv ?_
    refine max_eq_left (max_le hv'.1.1 ?_)
    exact mul_le_one' hv'.1.2 hv'.2
  refine ⟨(∏ w, cw w) * ∏ᶠ v, cv v, fun X x h1 h2 => ?_⟩
  unfold heightGL
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib,
    ← finprod_mul_distrib hfin (finite_mulSupport_htFin F x)]
  refine mul_le_mul' (Finset.prod_le_prod' fun w _ => ?_)
    (finprod_le_finprod' (finite_mulSupport_htFin F _) (hfin.union (finite_mulSupport_htFin F x) |>.subset
      (Function.mulSupport_mul _ _)) fun v => ?_)
  · refine htOf_le_mul (hcw1 w) _ _ ?_ ?_
    · rw [bc_val_aff _ _ _ _ h1]; exact hcw w _
    · rw [bc_inv_aff _ _ _ _ h2]; exact hcw w _
  · refine htOf_le_mul (le_max_left _ _) _ _ ?_ ?_
    · rw [bc_val_aff _ _ _ _ h1]; exact normFin_aff_le F v _ _ _ _
    · rw [bc_inv_aff _ _ _ _ h2]; exact normFin_aff_le F v _ _ _ _

end GlobalTheory.EmbHeight

namespace GlobalTheory.EmbHeight

open scoped NNReal
open GlobalTheory.AdelicU

theorem unitaryAdelicHeight_wittEmbedding_le : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ C : ℝ, ∀ g : GA D S₀,
    height S (d.emb0 g) ≤ C * height S₀ g := by
  intro D S S₀ ρ d
  obtain ⟨K, hK⟩ := exists_heightGL_aff_le D.host.F (d.jX ⬝ d.pX + d.jY ⬝ d.pY) d.j0 d.p0
  refine ⟨K, fun g => ?_⟩
  have h1 : ∀ g : GA D S₀, mt S (d.emb0 g) = (d.jX ⬝ d.pX + d.jY ⬝ d.pY) + d.j0 ⬝ mt S₀ g ⬝ d.p0 := fun g => by
    rw [d.unitaryMatrix_wittCoreEmbedding, add_right_comm]
  have h := hK (matHom S (d.emb0 g)) (matHom S₀ g) (h1 g) (by
    rw [← map_inv, ← map_inv]
    exact h1 g⁻¹)
  show ((heightGL D.host.F _ : ℝ≥0) : ℝ) ≤ (K : ℝ) * ((heightGL D.host.F _ : ℝ≥0) : ℝ)
  exact_mod_cast h

end GlobalTheory.EmbHeight

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_finitePart_denominator_le_height_pow : ∀ (D : D7) (V : HSp D), ∃ (C : ℝ) (A : ℕ), ∀ g : GA D V, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ C * height V g ^ A ∧ ∀ i j, (d : Lev.EAf D) * (Lev.finE V g).1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.PointDenom.exists_denom_le_height_pow | exact GlobalTheory.PointDenom.exists_denom_le_height_pow | (intros; apply GlobalTheory.PointDenom.exists_denom_le_height_pow <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal

namespace GlobalTheory.MixedTerm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev supWord (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (k : ℕ) (G : WO V W → ℂ) : ℝ≥0∞ :=
  GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) k G

theorem enorm_real_cast {a : ℝ} (h : 0 ≤ a) : ‖(a : ℂ)‖ₑ = ENNReal.ofReal a := by
  rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg h]

def opAlong (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) {r : ℕ}
    (C : Matrix (Fin V.rank) (Fin r) D.host.E) (x : Matrix (Fin W.rank) (Fin r) D.host.E) (G : WO V W → ℂ) : WO V W → ℂ :=
  G - (((4 * Real.pi ^ 2 : ℝ)⁻¹ : ℝ) : ℂ) • derAlong ψ θ V W C x (derAlong ψ θ V W C x G)

theorem theta_derAlong {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ)
    {V W : HSp D} {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (x : Matrix (Fin W.rank) (Fin r) D.host.E)
    {G : WO V W → ℂ} (hG : IsThetaFunO ψ V W G) : IsThetaFunO ψ V W (derAlong ψ θ V W C x G) := by
  obtain ⟨U, -, hU⟩ := GlobalTheory.Size.isTheta_iff_level.mp hG
  unfold derAlong
  exact GlobalTheory.Size.theta_finsetSum Finset.univ fun τ _ => (GlobalTheory.Size.dRho_mem_thetaLevel hψ hθ hU τ _).1

theorem theta_sub_smul {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {G H : WO V W → ℂ} (c : ℂ)
    (hG : IsThetaFunO ψ V W G) (hH : IsThetaFunO ψ V W H) : IsThetaFunO ψ V W (G - c • H) := by
  have h := GlobalTheory.OrientedHeis.theta_add hG (GlobalTheory.OrientedHeis.theta_smul (-c) hH)
  rwa [neg_smul, ← sub_eq_add_neg] at h

theorem term_opAlong {V V' W : HSp D} {r : ℕ} {C C' : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B) (h1 : adj D C * V.gram * C' = 1)
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ)
    {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)} (hμ : IsCovolOne (ratMx D W.rank r) μ 𝓨)
    {G : WO V W → ℂ} (hG : IsThetaFunO ψ V W G) (x y : Matrix (Fin W.rank) (Fin r) D.host.E) :
    term ψ V V' W C C' B μ 𝓨 (opAlong ψ θ V W C x G) y =
      ((1 + ratPair W y x ^ 2 : ℝ) : ℂ) * term ψ V V' W C C' B μ 𝓨 G y := by
  have hG1 := theta_derAlong hψ hθ C x hG
  have hG2 := theta_derAlong hψ hθ C x hG1
  obtain ⟨hadd, hsmul⟩ := GlobalTheory.T.mixedModelTerm_linear_thetaFunctions D V V' W r C C' B ψ hψ μ 𝓨 hμ y
  have e1 := GlobalTheory.T.mixedModelTerm_derivAlong_rational_pairing D V V' W r C C' B hs h1 ψ hψ θ hθ μ 𝓨 hμ G hG x y
  have e2 := GlobalTheory.T.mixedModelTerm_derivAlong_rational_pairing D V V' W r C C' B hs h1 ψ hψ θ hθ μ 𝓨 hμ _ hG1 x y
  have hsplit : opAlong ψ θ V W C x G = G + (-(((4 * Real.pi ^ 2 : ℝ)⁻¹ : ℝ) : ℂ)) •
      derAlong ψ θ V W C x (derAlong ψ θ V W C x G) := by
    rw [neg_smul, ← sub_eq_add_neg]
    rfl
  rw [hsplit, hadd _ _ hG (GlobalTheory.OrientedHeis.theta_smul _ hG2), hsmul _ _ hG2, e2, e1]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hc : (4 * (Real.pi : ℂ) ^ 2)⁻¹ * (4 * (Real.pi : ℂ) ^ 2) = 1 :=
    inv_mul_cancel₀ (mul_ne_zero (by norm_num) (pow_ne_zero 2 hπ))
  push_cast
  linear_combination (-(ratPair W y x : ℂ) ^ 2 * term ψ V V' W C C' B μ 𝓨 G y * Complex.I ^ 2) * hc +
    (-(ratPair W y x : ℂ) ^ 2 * term ψ V V' W C C' B μ 𝓨 G y) * Complex.I_sq

theorem term_decay {V V' W : HSp D} {r : ℕ} {C C' : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B) (h1 : adj D C * V.gram * C' = 1)
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ)
    {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)} (hμ : IsCovolOne (ratMx D W.rank r) μ 𝓨)
    (l : List (Matrix (Fin W.rank) (Fin r) D.host.E)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G → ∀ y,
      ‖term ψ V V' W C C' B μ 𝓨 G y‖ₑ * (l.map fun x => ENNReal.ofReal (1 + ratPair W y x ^ 2)).prod ≤
        ENNReal.ofReal K * supWord ψ θ V W (2 * l.length) G := by
  induction l with
  | nil =>
    refine ⟨1, zero_le_one, fun G _ y => ?_⟩
    simp only [List.map_nil, List.prod_nil, mul_one, ENNReal.ofReal_one, one_mul, List.length_nil,
      mul_zero]
    unfold supWord
    rw [GlobalTheory.Size.wordSum_zero]
    exact GlobalTheory.T.enorm_mixedModelTerm_le_iSup D V V' W r C C' B ψ hψ μ 𝓨 hμ G y
  | cons a l ih =>
    obtain ⟨K, hK, hb⟩ := ih
    obtain ⟨hsub, hder⟩ := GlobalTheory.T.supNormWordSum_sub_le_and_derivative_cost D V W ψ hψ θ hθ
    obtain ⟨c₀, hc₀, hd⟩ := hder r C a
    have he0 : (0 : ℝ) ≤ (4 * Real.pi ^ 2)⁻¹ := by positivity
    refine ⟨K * (1 + (4 * Real.pi ^ 2)⁻¹ * c₀ * c₀), by positivity, fun G hG y => ?_⟩
    have hG1 := theta_derAlong hψ hθ C a hG
    have hG2 := theta_derAlong hψ hθ C a hG1
    have hop : IsThetaFunO ψ V W (opAlong ψ θ V W C a G) :=
      theta_sub_smul ((((4 * Real.pi ^ 2 : ℝ)⁻¹ : ℝ) : ℂ)) hG hG2
    have hp : (0 : ℝ) ≤ 1 + ratPair W y a ^ 2 := by positivity
    have hterm : ‖term ψ V V' W C C' B μ 𝓨 (opAlong ψ θ V W C a G) y‖ₑ =
        ENNReal.ofReal (1 + ratPair W y a ^ 2) * ‖term ψ V V' W C C' B μ 𝓨 G y‖ₑ := by
      rw [term_opAlong hs h1 hψ hθ hμ hG a y, enorm_mul, enorm_real_cast hp]
    have hlen : 2 * (a :: l).length = 2 * l.length + 1 + 1 := by
      simp only [List.length_cons]
      ring
    have hsize : supWord ψ θ V W (2 * l.length) (opAlong ψ θ V W C a G) ≤
        ENNReal.ofReal (1 + (4 * Real.pi ^ 2)⁻¹ * c₀ * c₀) * supWord ψ θ V W (2 * (a :: l).length) G := by
      rw [hlen]
      have s1 := hsub G _ ((((4 * Real.pi ^ 2 : ℝ)⁻¹ : ℝ) : ℂ)) (2 * l.length) hG hG2
      have s2 := hd _ hG1 (2 * l.length)
      have s3 := hd G hG (2 * l.length + 1)
      have s4 := GlobalTheory.Size.wordSum_mono (A := GlobalTheory.Size.heisDer ψ θ)
        (p := fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) (show 2 * l.length ≤ 2 * l.length + 1 + 1 by omega) G
      rw [enorm_real_cast he0] at s1
      calc supWord ψ θ V W (2 * l.length) (opAlong ψ θ V W C a G)
          ≤ supWord ψ θ V W (2 * l.length) G + ENNReal.ofReal (4 * Real.pi ^ 2)⁻¹ *
              supWord ψ θ V W (2 * l.length) (derAlong ψ θ V W C a (derAlong ψ θ V W C a G)) := s1
        _ ≤ supWord ψ θ V W (2 * l.length + 1 + 1) G + ENNReal.ofReal (4 * Real.pi ^ 2)⁻¹ *
              (ENNReal.ofReal c₀ * (ENNReal.ofReal c₀ * supWord ψ θ V W (2 * l.length + 1 + 1) G)) := by
            gcongr
            exact s2.trans (by gcongr)
        _ = ENNReal.ofReal (1 + (4 * Real.pi ^ 2)⁻¹ * c₀ * c₀) * supWord ψ θ V W (2 * l.length + 1 + 1) G := by
            rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one,
              ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul he0]
            ring
    rw [List.map_cons, List.prod_cons]
    calc ‖term ψ V V' W C C' B μ 𝓨 G y‖ₑ * (ENNReal.ofReal (1 + ratPair W y a ^ 2) *
          (l.map fun x => ENNReal.ofReal (1 + ratPair W y x ^ 2)).prod)
        = ‖term ψ V V' W C C' B μ 𝓨 (opAlong ψ θ V W C a G) y‖ₑ *
          (l.map fun x => ENNReal.ofReal (1 + ratPair W y x ^ 2)).prod := by
          rw [hterm]
          ring
      _ ≤ ENNReal.ofReal K * supWord ψ θ V W (2 * l.length) (opAlong ψ θ V W C a G) := hb _ hop y
      _ ≤ ENNReal.ofReal K * (ENNReal.ofReal (1 + (4 * Real.pi ^ 2)⁻¹ * c₀ * c₀) *
          supWord ψ θ V W (2 * (a :: l).length) G) := by gcongr
      _ = ENNReal.ofReal (K * (1 + (4 * Real.pi ^ 2)⁻¹ * c₀ * c₀)) *
          supWord ψ θ V W (2 * (a :: l).length) G := by
          rw [ENNReal.ofReal_mul hK]
          ring

theorem mixed_terms_bound : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ A d : ℕ, ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) → ∃ K : ℝ, ∀ (g : GA D V) (h : GA D W) (F : WO V W → ℂ), IsThetaFunO ψ V W F → (∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ V W (actO V W g h u) F = F) → ∑' y : Matrix (Fin W.rank) (Fin r) D.host.E, ‖res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) F) 0‖ₑ ≤ ENNReal.ofReal (K * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ A) * GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) d F := by
  intro D V V' W r C C' B hs h1 _ _ ψ hψ θ hθ μ 𝓨 hμ
  obtain ⟨e, he⟩ := GlobalTheory.T.mixedModelTerm_bounded_denominators_moved_level D V V' W r C C' B hs h1 ψ hψ θ hθ μ 𝓨 hμ
  obtain ⟨n, X, hXint, hXsep⟩ := GlobalTheory.T.exists_integral_matrices_separating_rationalPairing D W r
  obtain ⟨K₀, hK₀, hdec⟩ := term_decay hs h1 hψ hθ hμ (List.ofFn X)
  refine ⟨2 * e * n, 2 * n, fun U hU => ?_⟩
  obtain ⟨M, _, hN⟩ := he U hU
  refine ⟨K₀ * (5 * (M : ℝ) ^ 2) ^ n, fun g h F hF hfix => ?_⟩
  obtain ⟨N, hNpos, hNle, hint⟩ := hN g h
  have hg1 := (GlobalTheory.Size.height_laws V).1 g
  have hh1 := (GlobalTheory.Size.height_laws W).1 h
  have ht0 : (0 : ℝ) ≤ GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h :=
    mul_nonneg (by linarith) (by linarith)
  have hbound := GlobalTheory.T.tsum_le_of_lattice_coords_quadraticDecay (Y := Matrix (Fin W.rank) (Fin r) D.host.E) n N hNpos
    (fun y => ‖term ψ V V' W C C' B μ 𝓨 F y‖ₑ) (fun j y => ratPair W y (X j))
    (fun y y' _ _ hyy => hXsep y y' hyy)
    (fun y hy j => hint F hF hfix y (enorm_ne_zero.mp hy) (X j) (hXint j))
    (ENNReal.ofReal K₀ * supWord ψ θ V W (2 * n) F)
    (fun y => by
      have hy := hdec F hF y
      rw [List.map_ofFn, List.prod_ofFn, List.length_ofFn] at hy
      exact hy)
  have hNM : (5 * (N : ℝ) ^ 2) ^ n ≤
      (5 * (M : ℝ) ^ 2) ^ n * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ (2 * e * n) := by
    calc (5 * (N : ℝ) ^ 2) ^ n
        ≤ (5 * ((M : ℝ) * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ e) ^ 2) ^ n := by gcongr
      _ = (5 * (M : ℝ) ^ 2) ^ n * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ (2 * e * n) := by ring
  show ∑' y, ‖term ψ V V' W C C' B μ 𝓨 F y‖ₑ ≤ _
  refine hbound.trans ?_
  calc ENNReal.ofReal K₀ * supWord ψ θ V W (2 * n) F * ENNReal.ofReal ((5 * (N : ℝ) ^ 2) ^ n)
      ≤ ENNReal.ofReal K₀ * supWord ψ θ V W (2 * n) F * ENNReal.ofReal ((5 * (M : ℝ) ^ 2) ^ n *
          (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ (2 * e * n)) := by gcongr
    _ = ENNReal.ofReal (K₀ * (5 * (M : ℝ) ^ 2) ^ n * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ (2 * e * n)) *
          supWord ψ θ V W (2 * n) F := by
        rw [mul_assoc K₀, ENNReal.ofReal_mul hK₀]
        ring

end GlobalTheory.MixedTerm

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun


theorem _root_.GlobalTheory.T.archLine_transposeGramUnitary_eq_exp : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (X : HSp D) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (hJ : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix (Equiv.refl (Fin X.rank)) (Equiv.refl (Fin X.rank))),
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Ws, ∃ L : GlobalTheory.SmoothForms.LieN X, ∀ t : ℝ,
      γ (Multiplicative.ofAdd t) = GlobalTheory.TripleRead.toUX X (Equiv.refl (Fin X.rank)) hJ (GlobalTheory.SmoothForms.expInf θ X (t • L)) := by
  first | exact @GlobalTheory.LineDecomp.line_eq_expInf | exact GlobalTheory.LineDecomp.line_eq_expInf | (intros; apply GlobalTheory.LineDecomp.line_eq_expInf <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

theorem GlobalTheory.PolMul.pol_mul_pairInf_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
        ∀ (q : (Fin n × Fin d → mixedEmbedding.mixedSpace F)), ∀ f ∈ M.Pol ψ τ, ∃ f₁ ∈ M.Pol ψ τ,
          ∀ x, f₁ x = (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) x q : ℂ) * f x := by
  intro F E _ _ _ _ _ σ _ n d X W M ψ χX χW om hψ _ _ _ _ _ _ _ _ _ τ _ _ q f hf
  exact GlobalTheory.PolMul.model_mul M ψ hψ τ q f hf
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.compactTorus_acts_fockVector_rowHighest : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ B, C.IsB B → ∀ f, C.IsTh f → C.IsFock B f → ∀ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ), C.toH Q ∈ Harm.rowHighest ℂ c c' → ∀ (ρ : D.what₂.Tau) (t : Fin T.rank → ℝ) (m : D.what₂.Tau → ℤ), RealScal C om B (torAt C.θ T B ρ t) (detPow C.θ T m (torAt C.θ T B ρ t)) → torAt C.θ T B ρ t ∈ GinfC T ∧ om (1, torAt C.θ T B ρ t) (C.fvec B f Q) = cexp (((∑ a, ((m ρ - ThFr.wtOf C.X C.hr c c' S.rank (C.m.e ρ) a : ℤ) : ℝ) * t a : ℝ) : ℂ) * I) • C.fvec B f Q := by
  first | exact @GlobalTheory.AdSpan.TorWt.torAt_fvec | exact GlobalTheory.AdSpan.TorWt.torAt_fvec | (intros; apply GlobalTheory.AdSpan.TorWt.torAt_fvec <;> assumption)
end
