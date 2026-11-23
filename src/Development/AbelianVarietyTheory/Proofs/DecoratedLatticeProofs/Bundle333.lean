module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle260
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle095
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle320
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle313
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle217
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle146
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle321
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle227
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle233
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle251
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousIsotropicSandwichMeanTranslation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CenFockWt

theorem central_wt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ k : KerDat S T, k.Is ψ θ x y → ∃ wt : (FVar D T.rank S.rank →₀ ℕ) → GA D S → ℂ, (∀ α, ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → ‖wt α z‖ = 1 ∧ ∀ c : WO S T →₀ ℂ, IsFinComb c → k.om (z, 1) (pureTensorO ψ θ S T x.s y.s x.B y.B (comb ψ S T c k.vac) (MvPolynomial.monomial α 1)) = wt α z • pureTensorO ψ θ S T x.s y.s x.B y.B (comb ψ S T c k.vac) (MvPolynomial.monomial α 1)) ∧ ∀ χ : GA D S → ℂ, {α | ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → wt α z = χ z}.Finite := by
  intro D ψ θ hθ S T x y hx hy k hk
  classical
  obtain ⟨χS, χT, hW⟩ := hk.weil
  have hstd : IsStdChar D ψ (-1) := hk.vac.1
  have hvth : IsThetaFunO ψ S T k.vac := hk.vac.2.theta
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_realCentre_character_on_definiteVacuum D ψ θ hθ S T x y hx hy k hk
  set ζ : GA D S → D.what₂.Tau → ℂ := fun z τ =>
    if h : 0 < S.rank then compAt θ τ (Formalism.L2.Theta.mt S z) ⟨0, h⟩ ⟨0, h⟩ else 1 with hζdef
  set μ : GA D S → D.what₂.Tau → ℂ := fun z τ => if (x.s τ = 1 ↔ y.s τ = 1) then (ζ z τ)⁻¹ else ζ z τ with hμdef
  set deg : D.what₂.Tau → (FVar D T.rank S.rank →₀ ℕ) → ℕ := fun τ α => ∑ v ∈ α.support with v.1 = τ, α v with hdeg
  have hζ : ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → ∀ τ,
      ‖ζ z τ‖ = 1 ∧ compAt θ τ (Formalism.L2.Theta.mt S z) = ζ z τ • (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) := by
    intro z hz hzc τ
    obtain ⟨ζ', h1, h2⟩ := GlobalTheory.T.realComponent_central_definiteUnitary_eq_unit_scalar D θ hθ S x hx z hz hzc τ
    by_cases h : 0 < S.rank
    · have e : ζ z τ = ζ' := by
        simp only [hζdef, dif_pos h, h2, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      rw [e]; exact ⟨h1, h2⟩
    · have e : ζ z τ = 1 := by simp only [hζdef, dif_neg h]
      refine ⟨by rw [e, norm_one], ?_⟩
      ext i
      exact absurd i.2 (by omega)
  have hμ : ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → ∀ τ, ‖μ z τ‖ = 1 := by
    intro z hz hzc τ
    simp only [hμdef]
    split_ifs
    · rw [norm_inv, (hζ z hz hzc τ).1, inv_one]
    · exact (hζ z hz hzc τ).1
  have hT1 : ∀ τ, compAt θ τ (Formalism.L2.Theta.mt T 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one T _
  have comb_smul : ∀ (cc : WO S T →₀ ℂ) (a : ℂ) (g : WO S T → ℂ), comb ψ S T cc (a • g) = a • comb ψ S T cc g := by
    intro cc a g
    unfold comb
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    have : heisO ψ S T u (a • g) = a • heisO ψ S T u g := by
      funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
    rw [this, smul_comm]
  refine ⟨fun α z => c z * ∏ τ, μ z τ ^ deg τ α, ?_, ?_⟩
  · intro α z hz hzc
    refine ⟨?_, ?_⟩
    · rw [norm_mul, (hc z hz hzc).1, one_mul, norm_prod]
      refine Finset.prod_eq_one fun τ _ => ?_
      rw [norm_pow, hμ z hz hzc τ, one_pow]
    · intro cc hcc
      set F := pureTensorO ψ θ S T x.s y.s x.B y.B with hF
      have hcomb : ∀ g, comb ψ S T cc g = ∑ i : Fin cc.support.card,
          cc (cc.support.equivFin.symm i) • heisO ψ S T (cc.support.equivFin.symm i) g := by
        intro g
        unfold comb
        rw [← Finset.sum_coe_sort]
        exact (Equiv.sum_comp cc.support.equivFin.symm (fun u => cc u • heisO ψ S T u g)).symm
      have key1 : ∀ g, IsThetaFunO ψ S T g → ∀ P, F (comb ψ S T cc g) P = comb ψ S T cc (F g P) := by
        intro g hg P
        rw [hcomb, hcomb]
        exact (GlobalTheory.T.heisenberg_combination_comm_fockPolynomialVectors D ψ θ S T hstd hθ x.s y.s x.B y.B g hg cc.support.card _ _
          (fun i => hcc _ (Finset.coe_mem _)) P).1.symm
      have hop := GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT k.om hW hθ x.s x.s x.B (fun τ => ζ z τ • x.B τ)
        y.s y.s y.B y.B z 1
        (fun τ => by rw [(hζ z hz hzc τ).2, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul])
        (fun τ => by rw [hT1, Matrix.mul_one, Matrix.one_mul])
        (fun τ => by rw [(hζ z hz hzc τ).2, Matrix.smul_mul, Matrix.one_mul])
        (fun τ => by rw [hT1, Matrix.one_mul]) k.vac hvth (MvPolynomial.monomial α 1)
      rw [key1 k.vac hvth, GlobalTheory.T.weilOperator_sourceRealPoint_commute_heisenbergComb D ψ S T χS χT k.om hW z hz cc hcc _ hop.1, hop.2, (hc z hz hzc).2,
        GlobalTheory.FiniteFock.pureTensorO_smul,
        GlobalTheory.T.pureTensorFock_unitScaledBasis_monomial D ψ θ hstd hθ S T x y hx hy k.vac hvth (ζ z) (fun τ => (hζ z hz hzc τ).1) α,
        smul_smul, comb_smul]
  · intro χ
    by_cases hne : ∃ α₀, ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → c z * ∏ τ, μ z τ ^ deg τ α₀ = χ z
    · obtain ⟨α₀, hα₀⟩ := hne
      refine (GlobalTheory.T.finite_monomials_with_prescribed_placeDegree D T.rank S.rank (fun τ => deg τ α₀)).subset fun α hα τ => ?_
      show deg τ α = deg τ α₀
      by_cases hr : 0 < S.rank ∧ 0 < T.rank
      · obtain ⟨z, hz, hzc, h1, h2⟩ := GlobalTheory.T.exists_central_realPoint_unit_scalar_single_place D θ hθ S τ (Complex.exp Complex.I) (by simpa using Complex.norm_exp_ofReal_mul_I 1)
        have e := (hα z hz hzc).trans (hα₀ z hz hzc).symm
        have hc0 : c z ≠ 0 := by
          intro h0
          have := (hc z hz hzc).1
          rw [h0, norm_zero] at this
          exact zero_ne_one this
        have e2 := mul_left_cancel₀ hc0 e
        have hζρ : ∀ ρ, ρ ≠ τ → ζ z ρ = 1 := by
          intro ρ hρ
          simp only [hζdef, dif_pos hr.1, h2 ρ hρ, Matrix.one_apply_eq]
        have hζτ : ζ z τ = Complex.exp Complex.I := by
          simp only [hζdef, dif_pos hr.1, h1, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
        have hμρ : ∀ ρ, ρ ≠ τ → μ z ρ = 1 := by
          intro ρ hρ
          simp only [hμdef, hζρ ρ hρ, inv_one, ite_self]
        rw [Finset.prod_eq_single τ (fun ρ _ hρ => by rw [hμρ ρ hρ, one_pow]) (by simp),
          Finset.prod_eq_single τ (fun ρ _ hρ => by rw [hμρ ρ hρ, one_pow]) (by simp)] at e2
        exact GlobalTheory.T.eq_of_pow_eq_pow_of_eq_exp_I_or_inv _ _ (μ z τ) (by
          simp only [hμdef, hζτ]
          split_ifs
          exacts [Or.inr rfl, Or.inl rfl]) e2
      · have hE : IsEmpty (FVar D T.rank S.rank) :=
          ⟨fun v => hr ⟨by have := v.2.2.2; omega, by have := v.2.1.2; omega⟩⟩
        simp only [hdeg, Finset.eq_empty_of_isEmpty α.support, Finset.eq_empty_of_isEmpty α₀.support,
          Finset.filter_empty, Finset.sum_empty]
    · refine Set.Finite.subset Set.finite_empty fun α hα => hne ⟨α, hα⟩

end GlobalTheory.CenFockWt
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

theorem castP_surjective {D : D7} {p q a b : ℕ} (hp : p = a) (hq : q = b) (Q : FP D.what₂.Tau a b) :
    ∃ P : PolF D q p, castP hp hq P = Q := by
  subst hp; subst hq
  refine ⟨Q, ?_⟩
  show MvPolynomial.rename _ Q = Q
  have : (fun v : D.what₂.Tau × Fin q × Fin p => (v.1, Fin.cast rfl v.2.1, Fin.cast rfl v.2.2)) = id := by
    funext v; simp
  rw [this, MvPolynomial.rename_id_apply]

theorem kBack_of_classData : ∀ (D : D7) (c : Comm D) (t : Tup c) (ρ : RealD c) (A : ClsK ρ t), c.Is → t.Is → ρ.Is → A.Is →
    (∀ j, j < D.R.m → t.cK j ≠ 0) → t.KBack := by
  intro D c t ρ A hc ht hρ hA hK j hj
  refine ⟨hK j hj, fun w => ?_⟩
  have hj1 : j + 1 ≤ D.R.m := hj
  have hab : ρ.N j ≤ ρ.N (j + 1) := (hρ.rk j hj).2
  obtain ⟨hB, ν, hν, -, hL⟩ := GlobalTheory.T.thetaLifts_all_charts_eq_classSum D c ρ hc hρ j hj1 hab
  haveI := hB
  haveI := hν
  set z : D.what₂.Tau → Matrix (Fin (ρ.N (j + 1))) (Fin (ρ.N (j + 1))) ℂ :=
    fun τ => (ρ.sc j τ)⁻¹ • (ρ.fr (j + 1) w).1 τ with hz
  obtain ⟨m, ys, Ps, hinv, havg⟩ := GlobalTheory.KJInf.subY_eq_sum_averages D.what₂.Tau (ρ.N j) (ρ.N (j + 1)) hab (ρ.lam j)
    (ρ.n j) (GinfC (c.X j)) ν (fun k => ρ.r j (Nat.le_of_succ_le hj1) k.1) (hρ.uni j _) z
  set s0 : ℂ := (∏ τ, ((ρ.fr (j + 1) w).1 τ).det ^ ρ.sD j τ)⁻¹ with hs0
  let y : Fin m → c.Fr j := fun i => (ρ.fr j).symm ⟨ys i, hinv i⟩
  have hy : ∀ i, (ρ.fr j (y i)).1 = ys i := fun i => congrArg Subtype.val ((ρ.fr j).apply_symm_apply ⟨ys i, hinv i⟩)
  have hP : ∀ i, ∃ P : PolF D (c.X (j + 1)).rank (c.X j).rank,
      castP (ρ.hN j (Nat.le_of_succ_le hj1)) (ρ.hN (j + 1) hj1) P = (s0 * ∏ τ, (ys i τ).det ^ ρ.sS j τ) • Ps i :=
    fun i => castP_surjective _ _ _
  choose P hP using hP
  refine ⟨m, y, P, fun ψ hψ γ => ?_⟩
  have hsc : ∀ (i : Fin 1) τ, (ρ.fr (j + 1) ((fun _ => w) i)).1 τ = ρ.sc j τ • (fun _ => z) i τ := by
    intro i τ
    simp only [hz]
    rw [smul_smul, mul_inv_cancel₀ (hρ.sc j τ), one_smul]
  have hav : ∀ F ∈ Vn (ρ.lam j) (ρ.n j), ∀ Λ : FP D.what₂.Tau (ρ.N j) (ρ.N (j + 1)) →ₗ[ℂ] ℂ,
      ∑ i, (∏ τ, ((ρ.fr j (y i)).1 τ).det ^ (-ρ.sS j τ)) *
        ∫ k, Λ (mvZ (fun τ => (ρ.r j (Nat.le_of_succ_le hj1) k.1 τ)⁻¹) (fun _ => 1)
          (castP (ρ.hN j (Nat.le_of_succ_le hj1)) (ρ.hN (j + 1) hj1) (P i))) *
          evalAt (fun τ => ρ.r j (Nat.le_of_succ_le hj1) k.1 τ * (ρ.fr j (y i)).1 τ) F ∂ν =
      ∑ i : Fin 1, (fun _ => s0) i * Λ (subY hab ((fun _ => z) i) F) := by
    intro F hF Λ
    clear hL
    have h0 := havg F hF Λ
    rw [Fin.sum_univ_one, ← h0, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (∏ τ, (ys i τ).det ^ (-ρ.sS j τ)) * ∏ τ, (ys i τ).det ^ ρ.sS j τ = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun τ _ => ?_
      rw [_root_.zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ (hinv i τ).ne_zero)]
    beta_reduce
    simp only [hy, hP, map_smul, smul_eq_mul, mul_assoc, integral_const_mul]
    linear_combination (s0 * ∫ k, Λ (mvZ (fun τ => (ρ.r j (Nat.le_of_succ_le hj1) k.1 τ)⁻¹) (fun _ => 1) (Ps i)) *
          evalAt (fun τ => ρ.r j (Nat.le_of_succ_le hj1) k.1 τ * ys i τ) F ∂ν) * e
  have hmain := hL m y P 1 (fun _ => z) (fun _ => w) (fun _ => s0) hsc hav t A ht hA ψ hψ γ
  have hs1 : s0 * ∏ τ, ((ρ.fr (j + 1) w).1 τ).det ^ ρ.sD j τ = 1 := by
    rw [hs0]
    refine inv_mul_cancel₀ (Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ ((ρ.fr (j + 1) w).2 τ).ne_zero)
  rw [hmain, Fin.sum_univ_one]
  simp only [hs1, one_smul]

end GlobalTheory.SeeSaw

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

theorem kerX_of_clsPinD : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), c.Is → (∀ s, (t s).Is) → ClsPinD t → KerX t := by
  intro D c 𝒯 t hc ht hP
  obtain ⟨ρ, hρ, hA⟩ := hP
  intro j hj y P
  have hj1 : j + 1 ≤ D.R.m := hj
  obtain ⟨hpos, hab⟩ := hρ.rk j hj
  obtain ⟨hB, ν, hν1, hνL, hmain⟩ := GlobalTheory.T.thetaLifts_all_charts_eq_classSum D c ρ hc hρ j hj1 hab
  obtain ⟨m', y', s, hinv, havg⟩ := @GlobalTheory.KJAvg.avg_span D.what₂.Tau _ (ρ.N j) (ρ.N (j + 1)) hab hpos (ρ.lam j) (ρ.n j)
    (GinfC (c.X j)) _ _ _ _ hB ν hν1 hνL (fun k τ => ρ.r j (Nat.le_of_succ_le hj1) k.1 τ) (hρ.uni j _) (ρ.fr j y).1
    (castP (ρ.hN j (Nat.le_of_succ_le hj1)) (ρ.hN (j + 1) hj1) P)
  have hz : ∀ i, ∀ τ, IsUnit ((fun τ => ρ.sc j τ • y' i τ) τ).det := by
    intro i τ
    simp only [Matrix.det_smul]
    exact (IsUnit.pow _ (Ne.isUnit (hρ.sc j τ))).mul (hinv i τ)
  let z : Fin m' → FrN D (ρ.N (j + 1)) := fun i => ⟨fun τ => ρ.sc j τ • y' i τ, hz i⟩
  let y'' : Fin m' → c.Fr (j + 1) := fun i => (ρ.fr (j + 1)).symm (z i)
  let cst : ℂ := ∏ τ, ((ρ.fr j y).1 τ).det ^ (-ρ.sS j τ)
  have key := hmain 1 (fun _ => y) (fun _ => P) m' y' y'' (fun i => cst * s i)
    (by intro i τ; simp only [y'', Equiv.apply_symm_apply]; rfl)
    (by
      intro F hF Λ
      rw [Fin.sum_univ_one, havg F hF Λ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring)
  refine ⟨∑ i, Finsupp.single (y'' i) (cst * s i * ∏ τ, ((ρ.fr (j + 1) (y'' i)).1 τ).det ^ ρ.sD j τ), ?_⟩
  intro s' ψ hψ γ
  obtain ⟨⟨A, hA'⟩, _⟩ := hA s'
  have h1 := key (t s') A (ht s') hA' ψ hψ γ
  rw [Fin.sum_univ_one] at h1
  rw [h1]
  congr 1
  change _ = Finsupp.sum _ (fun y' b => b • (t s').rd (j + 1) γ ((t s').K j ψ) y')
  rw [Finsupp.sum_finsetSum _ _ (fun y' b => b • (t s').rd (j + 1) γ ((t s').K j ψ) y')
    (fun _ => zero_smul ℂ _) (fun _ _ _ => add_smul _ _ _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.sum_single_index (h := fun y' b => b • (t s').rd (j + 1) γ ((t s').K j ψ) y') (zero_smul ℂ _)]

end GlobalTheory.SeeSaw
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.WeilSuperpos

variable {D : D7}

theorem pair_swap {S A B T : HSp D} (o : OrthDec S A B) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    (k : Ω → WO B T) (a : Ω → ℂ) (hk : Measurable k) (ha : Integrable a μ)
    (ν : Measure (WO A T)) [IsFiniteMeasure ν]
    (Φ : WO S T → ℂ) (hΦc : Continuous Φ) (CΦ : ℝ) (hΦ : ∀ x, ‖Φ x‖ ≤ CΦ)
    (g : WO A T → ℂ) (hgc : Continuous g) (Cg : ℝ) (hg : ∀ x, ‖g x‖ ≤ Cg) :
    ∫ u, (∫ w, a w * Φ ((o.resS T).symm (u, k w)) ∂μ) * star (g u) ∂ν =
      ∫ w, a w * ∫ u, Φ ((o.resS T).symm (u, k w)) * star (g u) ∂ν ∂μ := by
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : BorelSpace (WO A T) := ⟨rfl⟩
  haveI : BorelSpace (WO B T) := ⟨rfl⟩
  haveI : SFinite ν := @instSFiniteOfSigmaFinite _ _ ν (@IsFiniteMeasure.toSigmaFinite _ _ ν _)
  obtain ⟨-, -, hA2, -⟩ := lattice_Mx D T.rank A.rank
  obtain ⟨-, -, hB2, -⟩ := lattice_Mx D T.rank B.rank
  have hσ : Measurable fun q : WO A T × Ω => Φ ((o.resS T).symm (q.1, k q.2)) :=
    hΦc.measurable.comp ((o.continuous_resS_symm T).measurable.comp
      (measurable_fst.prodMk (hk.comp measurable_snd)))
  have hgm : Measurable fun q : WO A T × Ω => star (g q.1) :=
    (continuous_star.comp hgc).measurable.comp measurable_fst
  have h1 : Integrable (fun q : WO A T × Ω => a q.2) (ν.prod μ) := ha.comp_snd ν
  have hint : Integrable (Function.uncurry fun u w => a w * Φ ((o.resS T).symm (u, k w)) * star (g u))
      (ν.prod μ) := by
    refine (h1.norm.mul_const (CΦ * Cg)).mono' ?_ (Filter.Eventually.of_forall fun q => ?_)
    · exact (h1.aestronglyMeasurable.mul hσ.aestronglyMeasurable).mul hgm.aestronglyMeasurable
    · rcases q with ⟨u, w⟩
      simp only [Function.uncurry_apply_pair, norm_mul, norm_star]
      have hC : 0 ≤ CΦ := (norm_nonneg _).trans (hΦ 0)
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (hΦ _) (hg _) (norm_nonneg _) hC) (norm_nonneg _)
  calc ∫ u, (∫ w, a w * Φ ((o.resS T).symm (u, k w)) ∂μ) * star (g u) ∂ν
      = ∫ u, ∫ w, a w * Φ ((o.resS T).symm (u, k w)) * star (g u) ∂μ ∂ν := by
        congr 1; funext u; rw [integral_mul_const]
    _ = ∫ w, ∫ u, a w * Φ ((o.resS T).symm (u, k w)) * star (g u) ∂ν ∂μ := integral_integral_swap hint
    _ = ∫ w, a w * ∫ u, Φ ((o.resS T).symm (u, k w)) * star (g u) ∂ν ∂μ := by
        congr 1; funext w; rw [← integral_const_mul]; congr 1; funext u; ring

theorem exists_sfinite {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (a : Ω → ℂ) (ha : Integrable a μ) :
    ∃ s : Set Ω, SigmaFinite (μ.restrict s) ∧ ∀ X : Ω → ℂ, ∫ w, a w * X w ∂μ = ∫ w, a w * X w ∂(μ.restrict s) := by
  have hf := ha.aefinStronglyMeasurable
  refine ⟨hf.sigmaFiniteSet, hf.sigmaFinite_restrict, fun X => ?_⟩
  have hs : MeasurableSet hf.sigmaFiniteSet := hf.measurableSet
  have h0 : ∀ᵐ w ∂μ, w ∉ hf.sigmaFiniteSet → a w = 0 := by
    have := hf.ae_eq_zero_compl
    rw [Filter.EventuallyEq, ae_restrict_iff' hs.compl] at this
    exact this.mono fun w hw hws => hw hws
  exact (setIntegral_eq_integral_of_ae_compl_eq_zero (h0.mono fun w hw hws => by rw [hw hws, zero_mul])).symm

variable {ψ : AddChar (AF D.host.F) ℂ}

theorem comm_sfinite {S A B T : HSp D} (o : OrthDec S A B) {χ χ' : (AE D)ˣ →* Circle} {om : Om A T}
    (hW : IsWeilDatumO ψ A T χ χ' om) {F : WO S T → ℂ} (hF : IsThetaFunO ψ S T F)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ] (k : Ω → WO B T) (a : Ω → ℂ)
    (hk : Measurable k) (ha : Integrable a μ) (p : GA D A × GA D T) (u₀ : WO A T) :
    om p (fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂μ) u₀ =
      ∫ w, a w * om p (fun u => F ((o.resS T).symm (u, k w))) u₀ ∂μ := by
  have hψ := hW.std
  set H : WO S T → ℂ := fun x => om p (fun u => F ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1 with hH
  have hHt : IsThetaFunO ψ S T H := (GlobalTheory.T.weilOperator_oneVariable_keeps_thetaFunctions D ψ S A B T o F hF).1 χ χ' om hW p
  have hHs : ∀ u b, H ((o.resS T).symm (u, b)) = om p (fun u' => F ((o.resS T).symm (u', b))) u := by
    intro u b; simp only [hH, AddEquiv.apply_symm_apply]
  have hsl : ∀ b, IsThetaFunO ψ A T (fun u => F ((o.resS T).symm (u, b))) := by
    intro b
    have := GlobalTheory.T.isThetaFunction_superposition_orthogonalSlices D ψ hψ S A B T o F hF Unit (Measure.dirac ()) (fun _ => b) (fun _ => 1)
      measurable_const (integrable_const _)
    simpa using this
  set G : WO A T → ℂ := fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂μ with hGdef
  set R : WO A T → ℂ := fun u => ∫ w, a w * om p (fun u' => F ((o.resS T).symm (u', k w))) u ∂μ with hRdef
  have hG : IsThetaFunO ψ A T G := GlobalTheory.T.isThetaFunction_superposition_orthogonalSlices D ψ hψ S A B T o F hF Ω μ k a hk ha
  have hR' : R = fun u => ∫ w, a w * H ((o.resS T).symm (u, k w)) ∂μ := by
    funext u; simp only [hRdef, hHs]
  have hR : IsThetaFunO ψ A T R := by
    rw [hR']; exact GlobalTheory.T.isThetaFunction_superposition_orthogonalSlices D ψ hψ S A B T o H hHt Ω μ k a hk ha
  have hL : IsThetaFunO ψ A T (om p G) := hW.om_pres p G hG
  obtain ⟨v⟩ := GlobalTheory.Unf.Inhab.nonempty_volM D T.rank A.rank
  obtain ⟨hhaar, hfd, hvol⟩ := v.covol
  haveI := hhaar
  haveI : IsFiniteMeasure (v.μ.restrict v.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, hvol]; exact ENNReal.one_lt_top⟩
  have key : ∀ g, IsThetaFunO ψ A T g → thPair v.μ v.𝓕 (om p G) g = thPair v.μ v.𝓕 R g := by
    intro g hg
    have hg' : IsThetaFunO ψ A T (om p⁻¹ g) := hW.om_pres _ _ hg
    have hinv : om p (om p⁻¹ g) = g := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    obtain ⟨Cg, hCg⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded A T ψ hψ _ hg
    obtain ⟨Cg', hCg'⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded A T ψ hψ _ hg'
    obtain ⟨CF, hCF⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ hF
    obtain ⟨CH, hCH⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ hHt
    calc thPair v.μ v.𝓕 (om p G) g = thPair v.μ v.𝓕 (om p G) (om p (om p⁻¹ g)) := by rw [hinv]
      _ = thPair v.μ v.𝓕 G (om p⁻¹ g) := GlobalTheory.T.weilDatum_preserves_thetaFundamentalDomainPairing D ψ A T χ χ' om hW v p _ _ hG hg'
      _ = ∫ w, a w * thPair v.μ v.𝓕 (fun u => F ((o.resS T).symm (u, k w))) (om p⁻¹ g) ∂μ := by
          unfold thPair
          exact pair_swap o μ k a hk ha _ F hF.cont CF hCF _ hg'.cont Cg' hCg'
      _ = ∫ w, a w * thPair v.μ v.𝓕 (om p (fun u => F ((o.resS T).symm (u, k w)))) g ∂μ := by
          congr 1; funext w; congr 1
          rw [← GlobalTheory.T.weilDatum_preserves_thetaFundamentalDomainPairing D ψ A T χ χ' om hW v p _ _ (hsl _) hg', hinv]
      _ = ∫ w, a w * thPair v.μ v.𝓕 (fun u => H ((o.resS T).symm (u, k w))) g ∂μ := by
          simp only [hHs]
      _ = thPair v.μ v.𝓕 R g := by
          rw [hR']; unfold thPair
          exact (pair_swap o μ k a hk ha _ H hHt.cont CH hCH g hg.cont Cg hCg).symm
  have hd : IsThetaFunO ψ A T (om p G - R) := GlobalTheory.WeilVacMove.isTheta_sub hL hR
  have hkd := key _ hd
  obtain ⟨CL, hCL⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded A T ψ hψ _ hL
  obtain ⟨CR, hCR⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded A T ψ hψ _ hR
  obtain ⟨Cd, hCd⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded A T ψ hψ _ hd
  haveI : BorelSpace (WO A T) := ⟨rfl⟩
  have bint : ∀ f : WO A T → ℂ, Continuous f → ∀ C : ℝ, (∀ x, ‖f x‖ ≤ C) →
      Integrable (fun x => f x * star ((om p G - R) x)) (v.μ.restrict v.𝓕) := by
    intro f hf C hC
    refine (integrable_const (C * Cd)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (hf.mul (continuous_star.comp hd.cont)).aestronglyMeasurable
    · rw [norm_mul, norm_star]
      exact mul_le_mul (hC x) (hCd x) (norm_nonneg _) ((norm_nonneg _).trans (hC x))
  have h0 : ∫ x in v.𝓕, ((Complex.normSq ((om p G - R) x) : ℝ) : ℂ) ∂v.μ = 0 := by
    have e : ∀ x, ((Complex.normSq ((om p G - R) x) : ℝ) : ℂ) =
        om p G x * star ((om p G - R) x) - R x * star ((om p G - R) x) := by
      intro x
      rw [← sub_mul, ← Pi.sub_apply, Complex.star_def, Complex.mul_conj]
    simp only [e]
    rw [integral_sub (bint _ hL.cont CL hCL) (bint _ hR.cont CR hCR)]
    unfold thPair at hkd
    rw [hkd, sub_self]
  rw [integral_complex_ofReal] at h0
  have h1 : ∫ x in v.𝓕, Complex.normSq ((om p G - R) x) ∂v.μ = 0 := by exact_mod_cast h0
  have hnn : 0 ≤ᵐ[v.μ.restrict v.𝓕] fun x => Complex.normSq ((om p G - R) x) :=
    Filter.Eventually.of_forall fun x => Complex.normSq_nonneg _
  have hi : Integrable (fun x => Complex.normSq ((om p G - R) x)) (v.μ.restrict v.𝓕) := by
    refine (integrable_const (Cd * Cd)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (Complex.continuous_normSq.comp hd.cont).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq, sq]
      exact mul_le_mul (hCd x) (hCd x) (norm_nonneg _) ((norm_nonneg _).trans (hCd x))
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hi).1 h1
  have hae' : ∀ᵐ x ∂v.μ.restrict v.𝓕, (om p G - R) x = 0 :=
    hae.mono fun x hx => Complex.normSq_eq_zero.1 hx
  obtain ⟨i1, -, i3, -, i5, -⟩ := lattice_Mx D T.rank A.rank
  haveI := i1; haveI := i3; haveI := i5
  have hz := GlobalTheory.WeilVacMove.eq_zero_of_ae_fundamentalDomain (ratMx D T.rank A.rank) v.μ v.𝓕 hfd (om p G - R) hd.cont
    (GlobalTheory.WeilVacMove.norm_periodic hψ hd) hae'
  have := congrFun hz u₀
  rw [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
  exact this

theorem weil_comm_superpos : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A B T : HSp D) (o : OrthDec S A B) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om A T), IsWeilDatumO ψ A T χ χ' om → ∀ (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (k : Ω → WO B T) (a : Ω → ℂ), Measurable k → Integrable a μ → ∀ p, IsThetaFunO ψ S T (fun x => om p (fun u => F ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1) ∧ ∀ u₀, om p (fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂μ) u₀ = ∫ w, a w * om p (fun u => F ((o.resS T).symm (u, k w))) u₀ ∂μ := by
  intro D ψ S A B T o χ χ' om hW F hF Ω _ μ k a hk ha p
  refine ⟨(GlobalTheory.T.weilOperator_oneVariable_keeps_thetaFunctions D ψ S A B T o F hF).1 χ χ' om hW p, fun u₀ => ?_⟩
  obtain ⟨s, hs, hr⟩ := exists_sfinite μ a ha
  have e1 : (fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂μ) =
      fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂(μ.restrict s) := funext fun u => hr _
  rw [e1, hr]
  exact comm_sfinite o hW hF (μ.restrict s) k a hk ha.restrict p u₀

end GlobalTheory.WeilSuperpos
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaChainStep_weilDatum_nonzero_fockVacuum : ∀ D : D7, GlobalTheory.ChainOnto.ForStep D fun c k s s' p => ∀ hk : k < D.R.m, IsWeilExp c.ψ s.V s'.V (expS D ⟨k, hk⟩) (expT D ⟨k, hk⟩) p.ω ∧ IsVacVec c.ψ c.θ s.M s'.M p.f := by
  first | exact @GlobalTheory.ChainOnto.StepExp.stepExpVac | exact GlobalTheory.ChainOnto.StepExp.stepExpVac | (intros; apply GlobalTheory.ChainOnto.StepExp.stepExpVac <;> assumption)
end
