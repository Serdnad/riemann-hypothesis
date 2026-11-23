module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle141
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle163
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionIsotropicSplitSmoothRealPoints
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle008
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle121
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle164
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped GlobalTheory.MixModel

namespace GlobalTheory.WittSect

theorem sub_one_mulVec_eq_zero {R : Type*} [CommRing R] {n a b : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (P : Matrix (Fin n) (Fin a) R) (Q : Matrix (Fin n) (Fin b) R) (v : Fin n → R) (p : Fin a → R) (q : Fin b → R)
    (hv : v = P *ᵥ p + Q *ᵥ q) (hP : M * P = P) (hQ : M * Q = Q) : (M - 1) *ᵥ v = 0 := by
  rw [hv, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP, hQ,
    sub_self]

theorem exists_hypDec_mem_NI : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B →
    ∃ d : GlobalTheory.MixModel.HypDec V V' r, d.e = C ∧ d.i₀ = B ∧ ∀ m : GA D V,
      HMul.hMul (Formalism.L2.Theta.mt V m) (C.map (incA D)) = C.map (incA D) →
      HMul.hMul (Formalism.L2.Theta.mt V m) (B.map (incA D)) = B.map (incA D) → m ∈ NI V C := by
  intro D V V' r C B hs
  obtain ⟨C', h1, h2, h3⟩ := GlobalTheory.TwistDual.exists_isotropic_dual D V V' r C B hs
  have e : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D M = Mᴴ := fun _ => rfl
  have hG := GlobalTheory.MixModel.gram_conjTranspose V
  rw [e] at h1 h2 h3
  have hee : Cᴴ * V.gram * C = 0 := hs.frame.2.2
  have horth : Cᴴ * V.gram * B = 0 := by rw [← e]; exact hs.orth
  have hiso : Bᴴ * V.gram * B = V'.gram := by rw [← e]; exact hs.isom
  have h1' : C'ᴴ * V.gram * C = 1 := by
    have := congrArg Matrix.conjTranspose h1
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using this
  have h0e : Bᴴ * V.gram * C = 0 := by
    have := congrArg Matrix.conjTranspose horth
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using this
  have h0e' : Bᴴ * V.gram * C' = 0 := by
    have := congrArg Matrix.conjTranspose h3
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using this
  let d : GlobalTheory.MixModel.HypDec V V' r :=
    { e := C, e' := C', i₀ := B, ee := hee, e'e' := h2, e'e := h1', iso := hiso, i₀e := h0e, i₀e' := h0e',
      rank_add := hs.rank.symm }
  refine ⟨d, rfl, rfl, fun m hC hB => Subgroup.subset_closure ?_⟩

  have hu := GlobalTheory.MixModel.mt_unitary V m
  have hsum : C * (C'ᴴ * V.gram) + B * (V'.gram⁻¹ * (Bᴴ * V.gram)) + C' * (Cᴴ * V.gram) = 1 :=
    d.sum_eq_one_rat
  have hCm : GlobalTheory.MixModel.adj (C.map (incA D)) * GlobalTheory.MixModel.gA V * mt V m =
      GlobalTheory.MixModel.adj (C.map (incA D)) * GlobalTheory.MixModel.gA V := by
    calc GlobalTheory.MixModel.adj (C.map (incA D)) * GlobalTheory.MixModel.gA V * mt V m
        = GlobalTheory.MixModel.adj (mt V m * C.map (incA D)) * GlobalTheory.MixModel.gA V * mt V m := by rw [hC]
      _ = GlobalTheory.MixModel.adj (C.map (incA D)) * (GlobalTheory.MixModel.adj (mt V m) * (GlobalTheory.MixModel.gA V * mt V m)) := by
          simp only [GlobalTheory.MixModel.adj, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hu]
  simp only [Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_⟩
  · change (mt V m - 1) * C.map (incA D) = 0
    rw [Matrix.sub_mul, hC, Matrix.one_mul, sub_self]
  · rw [Matrix.map_mul]
    change GlobalTheory.MixModel.adj (C.map (incA D)) * GlobalTheory.MixModel.gA V * (mt V m - 1) = 0
    rw [Matrix.mul_sub, hCm, Matrix.mul_one, sub_self]
  · intro x hx
    refine ⟨0, ?_⟩
    rw [Matrix.mulVec_zero]
    have hx0 : (Cᴴ * V.gram) *ᵥ x = 0 := hx
    obtain ⟨u, hu⟩ : ∃ u, u = (C'ᴴ * V.gram) *ᵥ x := ⟨_, rfl⟩
    obtain ⟨w, hw⟩ : ∃ w, w = (V'.gram⁻¹ * (Bᴴ * V.gram)) *ᵥ x := ⟨_, rfl⟩
    have hx' : x = C *ᵥ u + B *ᵥ w := by
      have := congrArg (fun M => M *ᵥ x) hsum
      rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec (M := C),
        ← Matrix.mulVec_mulVec (M := B), ← Matrix.mulVec_mulVec (M := C'), hx0, Matrix.mulVec_zero, add_zero] at this
      rw [hu, hw]; exact this.symm
    have hxA : (fun i => incA D (x i)) = C.map (incA D) *ᵥ (incA D ∘ u) + B.map (incA D) *ᵥ (incA D ∘ w) := by
      funext i
      have hi : x i = (C *ᵥ u) i + (B *ᵥ w) i := congrFun hx' i
      have ha := RingHom.map_mulVec (incA D) C u i
      have hb := RingHom.map_mulVec (incA D) B w i
      rw [Pi.add_apply, ← ha, ← hb, hi]
      exact RingHom.map_add (incA D) _ _
    refine sub_one_mulVec_eq_zero _ (C.map (incA D)) (B.map (incA D)) _ (incA D ∘ u) (incA D ∘ w) ?_ ?_ ?_
    · exact hxA
    · exact hC
    · exact hB

end GlobalTheory.WittSect
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.restrictedHeisenbergTheta_continuous_bounded : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ f, IsThetaFunO ψ V W f → Continuous (fun p : WO V' W × Mx D W.rank r => GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' p.2) f) p.1) ∧ ∃ M : ℝ, ∀ x u, ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f) x‖ ≤ M := by
  first | exact @GlobalTheory.IndefiniteRowSideFullHecke.ResCont.res_heisO_continuous_bounded | exact GlobalTheory.IndefiniteRowSideFullHecke.ResCont.res_heisO_continuous_bounded | (intros; apply GlobalTheory.IndefiniteRowSideFullHecke.ResCont.res_heisO_continuous_bounded <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_homSpace_dual_isotropic_middle_decomposition : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∃ e : (Mx D W.rank r × Mx D W.rank r × WO V' W) ≃ₜ+ WO V W, (∀ t y x, e (t, y, x) = isoPart V W C' t + isoPart V W C y + midPart V V' W B x) ∧ ∀ t y x, e (t, y, x) ∈ ratL W V ↔ t ∈ ratMx D W.rank r ∧ y ∈ ratMx D W.rank r ∧ x ∈ ratL W V' := by
  first | exact @GlobalTheory.TwistDecomp.decomp_exists | exact GlobalTheory.TwistDecomp.decomp_exists | (intros; apply GlobalTheory.TwistDecomp.decomp_exists <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isotropicDualMiddleParts_symplectic_orthogonal : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → (∀ a b, symplO V W (isoPart V W C a) (isoPart V W C b) = 0) ∧ (∀ a x, symplO V W (isoPart V W C a) (midPart V V' W B x) = 0) ∧ (∀ a x, symplO V W (isoPart V W C' a) (midPart V V' W B x) = 0) ∧ (∀ a b, symplO V W (isoPart V W C' a) (isoPart V W C' b) = 0) := by
  first | exact @GlobalTheory.TwistFormsOrth.orthogonal | exact GlobalTheory.TwistFormsOrth.orthogonal | (intros; apply GlobalTheory.TwistFormsOrth.orthogonal <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaRestriction_isotropicSplit_smooth_realPoints : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), (∀ (y y' : Mx D W.rank r) (x x' : WO V' W), symplOH V W (isoPart V W C y + midPart V V' W B x) (isoPart V W C y' + midPart V V' W B x') = symplOH V' W x x') → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ f, IsThetaFunO ψ V W f → ∀ (k : ℕ) (L : (Fin k → ℝ) →+ WO V' W), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ∞ fun t => res V V' W C B μ 𝓨 f (w + L t) := by
  first | exact @GlobalTheory.TowerSmooth.res_smooth | exact GlobalTheory.TowerSmooth.res_smooth | (intros; apply GlobalTheory.TowerSmooth.res_smooth <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.LPositivity

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.UnitarySphericalReps
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)

section Analysis

theorem isPosReal_iff {z : ℂ} : IsPosReal z ↔ ∃ r : ℝ, 0 < r ∧ z = r :=
  ⟨fun h => ⟨z.re, h.2, Complex.ext rfl (by simpa using h.1)⟩, by rintro ⟨r, hr, rfl⟩; exact ⟨rfl, hr⟩⟩

theorem isPosReal_prod {ι : Type} (s : Finset ι) {f : ι → ℂ} (h : ∀ i ∈ s, IsPosReal (f i)) :
    IsPosReal (∏ i ∈ s, f i) := by
  refine Finset.prod_induction f IsPosReal (fun a b ha hb => ?_) ⟨rfl, one_pos⟩ h
  obtain ⟨x, hx, rfl⟩ := isPosReal_iff.1 ha
  obtain ⟨y, hy, rfl⟩ := isPosReal_iff.1 hb
  exact isPosReal_iff.2 ⟨x * y, mul_pos hx hy, by simp⟩

theorem isPosReal_of_hasProd {ι : Type} {f : ι → ℂ} {a : ℂ} (ha : HasProd f a) (h0 : a ≠ 0)
    (h : ∀ i, IsPosReal (f i)) : IsPosReal a := by
  have hc : IsClosed {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} :=
    (isClosed_eq Complex.continuous_im continuous_const).inter (isClosed_le continuous_const Complex.continuous_re)
  have := hc.mem_of_tendsto ha (Eventually.of_forall fun s =>
    ⟨(isPosReal_prod s fun i _ => h i).1, (isPosReal_prod s fun i _ => h i).2.le⟩)
  exact ⟨this.1, this.2.lt_of_ne fun e => h0 (Complex.ext e.symm this.1)⟩

theorem isPosReal_eulerFac {B : Multiset ℂˣ} {x : ℂ} (hB : B.map star = B) (hx : star x = x)
    (h : ∀ b ∈ B, ‖(b : ℂ) * x‖ < 1) : IsPosReal (eulerFac B x) := by
  have hre : ∀ b ∈ B, 0 < (1 - (b : ℂ) * x).re := fun b hb => by
    have := (Complex.re_le_norm _).trans_lt (h b hb)
    rw [Complex.sub_re, Complex.one_re]
    linarith
  set u : ℂ := (B.map fun b : ℂˣ => Complex.log (1 - (b : ℂ) * x)).sum with hu
  have h1 : eulerPoly B x = Complex.exp u := by
    rw [hu, Complex.exp_multiset_sum, Multiset.map_map, eulerPoly]
    refine congrArg _ (Multiset.map_congr rfl fun b hb => (Complex.exp_log fun e => ?_).symm)
    simpa [e] using hre b hb
  have h2 : starRingEnd ℂ u = u := by
    conv_rhs => rw [hu, ← hB, Multiset.map_map]
    rw [hu, map_multiset_sum, Multiset.map_map]
    refine congrArg _ (Multiset.map_congr rfl fun b hb => ?_)
    have h3 : (1 - (b : ℂ) * x).arg ≠ Real.pi := fun e => by
      have := (Complex.arg_eq_pi_iff.1 e).1
      linarith [hre b hb]
    simp only [Function.comp_apply, Units.coe_star]
    rw [← Complex.log_conj _ h3, map_sub, map_one, map_mul, show starRingEnd ℂ x = x from hx]
    rfl
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h2
  exact isPosReal_iff.2 ⟨(Real.exp r)⁻¹, by positivity, by rw [eulerFac, h1, hr]; simp⟩

variable {K : Type} [Field K] [NumberField K]

theorem star_npow (w : HeightOneSpectrum (𝓞 K)) (s : ℝ) : star (npow w (-(s : ℂ))) = npow w (-(s : ℂ)) := by
  rw [npow, ← Complex.ofReal_neg, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg _)]
  exact Complex.conj_ofReal _

theorem norm_lt_one_of_bounded {T : Set (HeightOneSpectrum (𝓞 K))} {c : Fam K} {r : ℕ} {κ : ℝ} (h : Bounded T c r κ)
    {s : ℂ} (hs : κ < s.re) {w : HeightOneSpectrum (𝓞 K)} (hw : w ∉ T) :
    ∀ b ∈ c w, ‖(b : ℂ) * npow w (-s)‖ < 1 := fun _ hb =>
  (h.norm_le le_rfl hw hb).trans_lt
    (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast one_lt_absNorm w) (by linarith))

end Analysis

section Normalising

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end Normalising

section Transport

variable {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

end Transport

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {h : w.under (𝓞 F) = v}
  {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GLoc σ J v) V} {B : Multiset ℂˣ}
  (hc : IsCMExt F E σ) (hJ : IsHermND σ J) (hL : Submodule.IsFullLattice E L) (hd : IsSelfDualAt σ J L v)

include hc hJ hL hd

theorem exists_inert_chart (h : w.under (𝓞 F) = v) (hv : IsInertAt F E v w) :
    ∃ c ϖ e, IsUnramInv ϖ c (qV F v) ∧ IsInertChart σ J L h c e ∧ Continuous e ∧ Continuous e.symm := by
  obtain ⟨-, ⟨c, hcj, -⟩, -, -, H⟩ := (exists_isInertChart σ hc v).2 w h hv
  obtain ⟨⟨ϖ, hU⟩, H⟩ := H c hcj
  obtain ⟨e, he⟩ := H n J L hJ hL.fg hL.span_eq_top hd
  exact ⟨c, ϖ, e, hU, he⟩


end Local

section Global

open Formalism.BasicNotions Formalism.BasicNotions.TH

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem split_or_inert (D : D7) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) ∨ IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w := by
  haveI := D.host.isCMField_hostE
  haveI := GlobalTheory.PlaceComp.unramified (E := D.host.E) D.sp.cm
  set v := w.under (𝓞 D.host.F) with hv
  rcases (GlobalTheory.quadratic_unramified_iff_inert_or_split D.host.F D.host.E (isCMExt_host D).2.2.1 v).1
    (fun u _ => Algebra.unramified_iff_forall.1 inferInstance ⟨u.asIdeal, u.isPrime⟩) with h | h
  · exact Or.inr ((h.isMaximal (Ideal.map_ne_bot_of_ne_bot v.ne_bot)).eq_of_le w.isPrime.ne_top Ideal.map_comap_le)
  · obtain ⟨P, Q, hne, e⟩ := Set.ncard_eq_two.1 h
    have hP : P ∈ v.asIdeal.primesOver (𝓞 D.host.E) := by simp [e]
    have hQ : Q ∈ v.asIdeal.primesOver (𝓞 D.host.E) := by simp [e]
    have := hP.2
    have := hQ.2
    exact Or.inl ⟨⟨P, hP.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩,
      ⟨Q, hQ.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, fun e => hne (congrArg (·.asIdeal) e),
      hP.2.over.symm, hQ.2.over.symm⟩

variable {D : D7} {V : HSp D}

theorem star_eq_inv {z : ℂˣ} (h : ‖(z : ℂ)‖ = 1) : star z = z⁻¹ :=
  Units.ext (by simpa using (Complex.inv_eq_conj h).symm)

end Global

end GlobalTheory.LPositivity

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Twist.rowTest_complexSide_of_hilbert_models

theorem rowTest_toCx3 : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.RowTestModel R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F h
  obtain ⟨n, ψ, hinj, hrat⟩ := (GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.test_tw_iff (E := R.HE.H) (twAt D.what₂.embLL A3.A.v0) R.emb0 (ι := T0)
    (X := fun t => A3.A.fam.amb.FR t) fun t x => R.Th t (R.jX t x)).2 h
  exact ⟨n, ψ, hinj, fun t i x => hrat t x i⟩

end GlobalTheory.Twist.rowTest_complexSide_of_hilbert_models
end

section


theorem _root_.GlobalTheory.T.unramifiedDoublingIntegral_inert_place : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.UnramDoublingInert := by
  first | exact @GlobalTheory.InertZeta.unramDoublingInert | exact GlobalTheory.InertZeta.unramDoublingInert | (intros; apply GlobalTheory.InertZeta.unramDoublingInert <;> assumption)
end

section

namespace GlobalTheory.SubstitutionFinitelyGenerated

theorem fg_of_vars {σ ι : Type*} (φ : ι → MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ)
    (h : ∀ v, ∃ U : Submodule ℂ (MvPolynomial σ ℂ), U.FG ∧ ∀ i, φ i (MvPolynomial.X v) ∈ U)
    (P : MvPolynomial σ ℂ) : ∃ V : Submodule ℂ (MvPolynomial σ ℂ), V.FG ∧ ∀ i, φ i P ∈ V := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    refine ⟨Submodule.span ℂ {MvPolynomial.C c}, Submodule.fg_span_singleton _, fun i => ?_⟩
    have : φ i (MvPolynomial.C c) = MvPolynomial.C c := (φ i).commutes c
    rw [this]
    exact Submodule.mem_span_singleton_self _
  | add p q hp hq =>
    obtain ⟨V₁, h₁, h₁'⟩ := hp
    obtain ⟨V₂, h₂, h₂'⟩ := hq
    refine ⟨V₁ ⊔ V₂, h₁.sup h₂, fun i => ?_⟩
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (h₁' i) (h₂' i)
  | mul_X p v hp =>
    obtain ⟨V₁, h₁, h₁'⟩ := hp
    obtain ⟨V₂, h₂, h₂'⟩ := h v
    refine ⟨V₁ * V₂, h₁.mul h₂, fun i => ?_⟩
    rw [map_mul]
    exact Submodule.mul_mem_mul (h₁' i) (h₂' i)

theorem subst_mem_fg : ∀ {D : Formalism.BasicNotions.D7} {a b : ℕ} (τ : Formalism.BasicNotions.Rows.Data.Tau (Formalism.BasicNotions.D7.what₂ D)) (ε : Fin a → Bool) (ε' : Fin b → Bool) (P : Formalism.IndefR.Links.PolF D b a), ∃ (V : Submodule ℂ (Formalism.IndefR.Links.PolF D b a)), Submodule.FG V ∧ ∀ (g : Matrix (Fin a) (Fin a) ℂ) (k : Matrix (Fin b) (Fin b) ℂ), (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.subst τ ε ε' g k : Formalism.IndefR.Links.PolF D b a → Formalism.IndefR.Links.PolF D b a) P ∈ V := by
  intro D a b τ ε ε' P
  obtain ⟨V, hV, hV'⟩ := fg_of_vars
    (fun gk : Matrix (Fin a) (Fin a) ℂ × Matrix (Fin b) (Fin b) ℂ => GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.subst τ ε ε' gk.1 gk.2) (by
      intro v
      refine ⟨Submodule.span ℂ (insert (MvPolynomial.X v)
        (Set.range fun lm : Fin b × Fin a => MvPolynomial.X (τ, lm.1, lm.2))),
        Submodule.fg_span ((Set.finite_range _).insert _), fun gk => ?_⟩
      unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.subst
      rw [MvPolynomial.aeval_X]
      by_cases hv : v.1 = τ
      · rw [if_pos hv]
        refine Submodule.sum_mem _ fun l _ => Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ ?_
        exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨(l, m), rfl⟩)
      · rw [if_neg hv]
        exact Submodule.subset_span (Set.mem_insert _ _)) P
  exact ⟨V, hV, fun g k => hV' (g, k)⟩

end GlobalTheory.SubstitutionFinitelyGenerated
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix GlobalTheory.Chain GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Chain.RealIt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev LPol (b a : ℕ) : Type := MvPolynomial (Fin b × Fin a) ℂ

section Local

variable {a b : ℕ} (ε : Fin a → Bool) (ε' : Fin b → Bool)

def rai (i : Fin b) (j : Fin a) : Module.End ℂ (LPol b a) :=
  sgn (ε j) • (if ε' i = ε j then LinearMap.mulLeft ℂ (MvPolynomial.X (i, j))
    else -(MvPolynomial.pderiv (i, j)).toLinearMap)

def low (i : Fin b) (j : Fin a) : Module.End ℂ (LPol b a) :=
  sgn (ε j) • (if ε' i = ε j then (MvPolynomial.pderiv (i, j)).toLinearMap
    else LinearMap.mulLeft ℂ (MvPolynomial.X (i, j)))

def locS (X : Matrix (Fin a) (Fin a) ℂ) : Module.End ℂ (LPol b a) :=
  ∑ j, ∑ k, X j k • ∑ i, (rai ε ε' i j * low ε ε' i k + if j = k then (1 / 2 : ℂ) • 1 else 0)

def locT (Y : Matrix (Fin b) (Fin b) ℂ) : Module.End ℂ (LPol b a) :=
  ∑ i, ∑ l, Y i l • ∑ j, (rai ε ε' i j * low ε ε' l j + if i = l then (1 / 2 : ℂ) • 1 else 0)

def IsPolyIso {p q r s : ℕ} (e : Ix p q ≃ Fin a) (e' : Ix r s ≃ Fin b) (κ : LPol b a ≃ₗ[ℂ] Pol p q r s) : Prop :=
  (∀ (Z : Mat p q) (P : LPol b a), κ (locS ε ε' (Matrix.reindex e e Z) P) = fockAct1 p q r s Z (κ P)) ∧
    ∀ (Z : Mat r s) (P : LPol b a), κ (locT ε ε' (Matrix.reindex e' e' Z) P) = fockAct2 p q r s Z (κ P)

end Local

structure IsCoverIt {p q r s : ℕ} {T₁ : GrpData p q} {T₂ : GrpData r s} (R₁ : DSRep T₁) (R₂ : DSRep T₂)
    (B : Pol p q r s →ₗ[ℂ] R₂.U.H →ₛₗ[starRingEnd ℂ] R₁.U.H) : Prop where
  bdd : ∀ P, ∃ c : ℝ, ∀ y, ‖B P y‖ ≤ c * ‖y‖
  kfin : ∀ P y, B P y ∈ Set.range R₁.ι
  ne : ∀ y, y ≠ 0 → ∃ P, B P y ≠ 0
  src : ∀ Z ∈ upq p q, ∀ P y,
    HasDerivAt (fun t : ℝ => R₁.U.π (T₁.expt (t • Z)) (B P y)) (B (fockAct1 p q r s Z P) y) 0
  tgt : ∀ Z ∈ upq r s, ∀ P y,
    HasDerivAt (fun t : ℝ => B P (R₂.U.π (T₂.expt (t • Z)) y)) (-B (fockAct2 p q r s Z P) y) 0

variable {D : D7}

def glue {a b : ℕ} (P : D.what₂.Tau → LPol b a) : PolF D b a :=
  ∏ τ, MvPolynomial.rename (fun s => (τ, s)) (P τ)


open Classical in
def GlueLaw (D : D7) (a b : ℕ) : Prop :=
  Submodule.span ℂ (Set.range (glue : (D.what₂.Tau → LPol b a) → PolF D b a)) = ⊤ ∧
    ∀ (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (P : D.what₂.Tau → LPol b a),
      (∀ X, fockS τ ε ε' X (glue P) = glue (Function.update P τ (locS ε ε' X (P τ)))) ∧
        ∀ Y, fockT τ ε ε' Y (glue P) = glue (Function.update P τ (locT ε ε' Y (P τ)))

variable {V W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S')

structure LocIt (τ : D.what₂.Tau) (aS aT : ℚ) (A : LPol W.rank V.rank →ₗ[ℂ] M'.H τ →ₗ[ℂ] M.H τ) : Prop where
  sm : ∀ P y, A P y ∈ M.sm τ
  ne : ∃ P, ∃ y ∈ M'.sm τ, A P y ≠ 0
  adj : ∀ P w, ∃ w', ∀ y, ⟪w, A P y⟫_ℂ = ⟪w', y⟫_ℂ
  src : ∀ X ∈ lieAt V τ, ∀ P y, HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (A P y))
    (A (locS (M.ε τ) (M'.ε τ) ((M.fr τ * X * (M.fr τ)⁻¹).map (starRingEnd ℂ)) P - ((aT : ℂ) * X.trace) • P) y) 0
  tgt : ∀ Y ∈ lieAt W τ, ∀ P y, HasDerivAt (fun t : ℝ => A P (M'.rep τ (NormedSpace.exp (t • Y)) y))
    (-A (locT (M.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) P + ((aS : ℂ) * Y.trace) • P) y) 0

def srcOp (τ : D.what₂.Tau) (aT : ℚ) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) : Module.End ℂ (PolF D W.rank V.rank) :=
  fockS τ (M.ε τ) (M'.ε τ) ((M.fr τ * X * (M.fr τ)⁻¹).map (starRingEnd ℂ)) + (-((aT : ℂ) * X.trace)) • 1

def tgtOp (τ : D.what₂.Tau) (aS : ℚ) (Y : Matrix (Fin W.rank) (Fin W.rank) ℂ) : Module.End ℂ (PolF D W.rank V.rank) :=
  fockT τ (M.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) + ((aS : ℂ) * Y.trace) • 1

structure GlobIt (aS aT : D.what₂.Tau → ℚ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M)
    (I : PolF D W.rank V.rank →ₗ[ℂ] (⨂[ℂ] τ, M'.H τ) →ₗ[ℂ] ⨂[ℂ] τ, M.H τ) : Prop where
  incl : ∀ φ v, inclT M (It φ v) = I φ (inclT M' v)
  ne : It ≠ 0
  adj : ∀ φ w, ellT M w ∘ₗ I φ ∈ Submodule.span ℂ (Set.range (ellT M'))
  src : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ x w,
    HasDerivAt (fun t : ℝ => ellT M w (actT M τ (NormedSpace.exp (t • X)) (I φ x)))
      (ellT M w (I (srcOp M M' τ (aT τ) X φ) x)) 0
  tgt : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ x w,
    HasDerivAt (fun t : ℝ => ellT M w (I φ (actT M' τ (NormedSpace.exp (t • Y)) x)))
      (-ellT M w (I (tgtOp M M' τ (aS τ) Y φ) x)) 0

structure TensorLaw : Prop where
  sep : ∀ x : ⨂[ℂ] τ, M.H τ, (∀ w, ellT M w x = 0) → x = 0
  inj : Function.Injective (inclT M)
  one : ∀ τ, actT M τ 1 = LinearMap.id
  mul : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
    actT M τ (g * g') = actT M τ g ∘ₗ actT M τ g'
  adj : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, ∃ w', ellT M w ∘ₗ actT M τ g = ellT M w'

def ChosenSeries (X : ProvA) : Prop :=
  ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → HasParam (X.ds p q lam) lam

end GlobalTheory.Chain.RealIt

end
end
