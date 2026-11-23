module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle034
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle037
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem _root_.GlobalTheory.T.isStabiliserInvariant_pull_bounded_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X' X : Data E r) (h : SameSp X' X) (ga : GL (Fin r) E) (la' : Wt X'.Ψ r) (la : Wt X.Ψ r) (Δ : Subgroup (GL (Fin r) E)) (M : ℕ) (P : Frame X'.Ψ r → ℂ), IsUn X ga → (∀ (τ : X.Ψ) i, la τ i = la' ⟨τ.1, by rw [h.psi]; exact τ.2⟩ i) → (∀ g' ∈ Δ, IsUn X g' ∧ (mapL g' (mapL ga X'.Λ) = mapL ga X'.Λ → ∀ u ∈ mapL ga X'.Λ, ∃ u' ∈ mapL ga X'.Λ, (g' : Matrix (Fin r) (Fin r) E) *ᵥ u = u + M • u')) → HasPrinc X' M → ChiOne X' la' → X'.IsBddSec la' P → IsStabForm X Δ (mapL ga X'.Λ) la (fun x => P (castFr h.psi.symm (lact ga⁻¹ x))) ∧ ∀ Q : Frame X.Ψ r → ℂ, DifferentiableOn ℂ Q X.dom → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Q (rmul x b) = bchar la b * Q x) → DifferentiableOn ℂ (fun x => Q (lact ga (castFr h.psi x))) X'.dom ∧ ∀ x ∈ X'.dom, lact ga (castFr h.psi x) ∈ X.dom ∧ castFr h.psi.symm (lact ga⁻¹ (lact ga (castFr h.psi x))) = x ∧ ∀ b ∈ Bor X'.Ψ r, Q (lact ga (castFr h.psi (rmul x b))) = bchar la' b * Q (lact ga (castFr h.psi x)) := by
  first | exact @GlobalTheory.Dict.isStabForm_pull | exact GlobalTheory.Dict.isStabForm_pull | (intros; apply GlobalTheory.Dict.isStabForm_pull <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.HeisDeriv

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis

variable {D : D7} {S T : HSp D}

theorem EFR_conj (C : Ctx S T) (x y : RW T S) :
    EFR C.X (fun σ k a => conj (x (C.m.e.symm σ) a k) : WR C.X S.rank) (fun σ k a => conj (y (C.m.e.symm σ) a k)) =
      -omO S T x y := by
  simp only [EFR, hermC, omO, LinearMap.mk₂_apply, formAt]
  rw [← C.m.e.sum_comp, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [Equiv.symm_apply_apply, C.m.e_emb, C.m.ka, C.m.gT, C.m.gS, inv_one,
    ComplexEmbedding.conjugate_coe_eq, Matrix.transpose_apply, RCLike.conj_conj]
  have hx : (-(2 * D.host.xi0 / 2)) = -D.host.xi0 := by ring
  have hone : ∀ F : Fin S.rank → Fin S.rank → ℂ,
      ∑ a, ∑ b, tauE D τ ((1 : Matrix (Fin S.rank) (Fin S.rank) D.host.E) a b) * F a b = ∑ a, F a a := by
    intro F; simp [Matrix.one_apply]
  rw [hx]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [hone, ← Complex.re_sum, ← Finset.mul_sum]
  have hc : conj (tauE D τ (-D.host.xi0)) *
      ∑ k, ∑ a, conj (x τ a k) * ∑ b, conj (tauE D τ (T.gram b a)) * y τ b k =
      conj (-(tauE D τ D.host.xi0 *
        ∑ k, ∑ b, conj (y τ b k) * ∑ a, tauE D τ (T.gram b a) * x τ a k)) := by

    simp only [map_neg, map_mul, map_sum, RCLike.conj_conj, neg_mul]
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [hc, Complex.conj_re, Complex.neg_re]
  ring

theorem pi_lineAt {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    piW θ T S (lineAt θ τ z 1) = (Pi.single τ z : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) := by
  obtain ⟨-, -, h⟩ := isLineAt_lineAt hθ τ z
  funext τ' i j
  have h1 := congrFun (congrFun (h 1 τ') i) j
  rw [Pi.single_apply]
  split_ifs at h1 ⊢ with hτ
  · rw [Complex.ofReal_one, one_smul] at h1
    exact h1
  · exact h1

theorem single_conj (C : Ctx S T) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank) =
      fun σ k a => conj (piW C.θ T S (lineAt C.θ τ z 1) (C.m.e.symm σ) a k) := by
  rw [pi_lineAt C.inf]
  funext σ k a
  simp only [Pi.single_apply, Equiv.symm_apply_eq]
  split_ifs <;> simp

theorem dRho_laws : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ f, C.IsTh f → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), C.IsTh (dRho (heisO C.ψ S T) C.θ τ z f) ∧ (∀ w, HasDerivAt (fun t : ℝ => C.rho (lineAt C.θ τ z t) f w) (dRho (heisO C.ψ S T) C.θ τ z f w) 0) ∧ (∀ f', C.IsTh f' → dRho (heisO C.ψ S T) C.θ τ z (f + f') = dRho (heisO C.ψ S T) C.θ τ z f + dRho (heisO C.ψ S T) C.θ τ z f') ∧ (∀ a : ℂ, dRho (heisO C.ψ S T) C.θ τ z (a • f) = a • dRho (heisO C.ψ S T) C.θ τ z f) ∧ (∀ z', dRho (heisO C.ψ S T) C.θ τ (z + z') f = dRho (heisO C.ψ S T) C.θ τ z f + dRho (heisO C.ψ S T) C.θ τ z' f) ∧ (∀ t : ℝ, dRho (heisO C.ψ S T) C.θ τ ((t : ℂ) • z) f = (t : ℂ) • dRho (heisO C.ψ S T) C.θ τ z f) ∧ (∀ u, IsFinPt u → dRho (heisO C.ψ S T) C.θ τ z (C.rho u f) = C.rho u (dRho (heisO C.ψ S T) C.θ τ z f)) ∧ ∀ (τ' : D.what₂.Tau) (z' : Matrix (Fin T.rank) (Fin S.rank) ℂ), dRho (heisO C.ψ S T) C.θ τ z (dRho (heisO C.ψ S T) C.θ τ' z' f) - dRho (heisO C.ψ S T) C.θ τ' z' (dRho (heisO C.ψ S T) C.θ τ z f) = (2 * π * I * (EFR C.X (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank) (Pi.single (C.m.e τ') (fun k a => conj (z' a k)) : WR C.X S.rank) : ℝ)) • f := by
  intro D S T C f hf τ z
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart C.inf
  have hθ := C.inf
  have hψ := C.std
  have hD' : ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (g : WO S T → ℂ),
      dRho (heisO C.ψ S T) C.θ τ z g =
        hD (iotaW σ T S) (piW C.θ T S) (omO S T) (piW C.θ T S (lineAt C.θ τ z 1)) g := by
    intro τ z g
    rw [dRho_eq_dLine, dLine_eq_hD hσ hψ (isRealDir_lineAt hθ τ z)]
  have hsm : ∀ g, C.IsTh g → Sm (iotaW σ T S) g := fun g hg => theta_sm hσ hg
  have hform : ∀ g, C.IsTh g → ∀ (u : RW T S) (w : WO S T),
      hD (iotaW σ T S) (piW C.θ T S) (omO S T) u g w =
        -(Real.pi * Complex.I) * (omO S T (piW C.θ T S w) u : ℝ) * g w +
          fderiv ℝ (fun x : RW T S => g (w + iotaW σ T S x)) 0 u :=
    fun g hg u w => hD_eq_fderiv _ _ _ g (hsm g hg) u w
  have hdiff : ∀ g, C.IsTh g → ∀ w : WO S T,
      DifferentiableAt ℝ (fun x : RW T S => g (w + iotaW σ T S x)) 0 :=
    fun g hg w => ((hsm g hg w).differentiable (by simp)) 0
  refine ⟨theta_dRho hθ hψ τ z hf, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w
    have h := hasDerivAt_heisO hθ hψ (isRealDir_lineAt hθ τ z) hf w 0
    rw [map_zero, heisO_zero, ← dRho_eq_dLine] at h
    exact h
  · intro f' hf'
    funext w
    rw [hD', hD', hD', Pi.add_apply, hform f hf, hform f' hf', hform (f + f') (theta_add hf hf')]
    rw [show (fun x : RW T S => (f + f') (w + iotaW σ T S x)) =
        (fun x => f (w + iotaW σ T S x)) + (fun x => f' (w + iotaW σ T S x)) from rfl,
      fderiv_add (hdiff f hf w) (hdiff f' hf' w)]
    simp only [Pi.add_apply, _root_.add_apply]
    ring
  · intro a
    funext w
    rw [hD', hD', Pi.smul_apply, hform f hf, hform (a • f) (theta_smul a hf)]
    rw [show (fun x : RW T S => (a • f) (w + iotaW σ T S x)) =
        (fun x => a * f (w + iotaW σ T S x)) from rfl, fderiv_const_mul (hdiff f hf w)]
    simp only [Pi.smul_apply, smul_eq_mul, _root_.smul_apply]
    ring
  · intro z'
    have hadd : piW C.θ T S (lineAt C.θ τ (z + z') 1) =
        piW C.θ T S (lineAt C.θ τ z 1) + piW C.θ T S (lineAt C.θ τ z' 1) := by
      funext τ' i j
      have e := fun y : Matrix (Fin T.rank) (Fin S.rank) ℂ =>
        congrFun (congrFun (congrFun (pi_lineAt hθ τ y) τ') i) j
      rw [Pi.add_apply, Pi.add_apply, Pi.add_apply, e, e, e]
      simp only [Pi.single_apply]
      split_ifs <;> simp
    funext w
    rw [hD', hD', hD', Pi.add_apply, hform f hf, hform f hf, hform f hf, hadd, map_add (f := _),
      ContinuousLinearMap.map_add]
    push_cast
    ring
  · intro t
    have hs : piW C.θ T S (lineAt C.θ τ ((t : ℂ) • z) 1) = t • piW C.θ T S (lineAt C.θ τ z 1) := by
      funext τ' i j
      have e := fun y : Matrix (Fin T.rank) (Fin S.rank) ℂ =>
        congrFun (congrFun (congrFun (pi_lineAt hθ τ y) τ') i) j
      rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, e, e]
      simp only [Pi.single_apply]
      split_ifs <;> simp [Complex.real_smul]
    funext w
    rw [hD', hD', Pi.smul_apply, hform f hf, hform f hf, hs, map_smul, ContinuousLinearMap.map_smul]
    simp only [smul_eq_mul, Complex.real_smul]
    push_cast
    ring
  · intro u hu
    exact GlobalTheory.FinTranslate.dRho_heisO hθ hu τ z f
  · intro τ' z'
    have hskew : ∀ u v : RW T S, omO S T v u = -omO S T u v := by
      intro u v
      have h := omO_self hσ (u + v)
      simp only [map_add (f := _), LinearMap.add_apply, omO_self hσ, zero_add, add_zero] at h
      linarith
    simp only [hD']
    rw [heisenberg_derivative_commutator (WO S T) (RW T S) (iotaW σ T S) (piW C.θ T S) (omO S T)
      (hσ.pi_iota T S) (fun g hg u w => hD_eq_fderiv _ _ _ g hg u w) hskew f (hsm f hf),
      single_conj C τ z, single_conj C τ' z', EFR_conj]
    congr 1
    push_cast
    ring

end GlobalTheory.Ker.HeisDeriv
end

section

noncomputable section

namespace GlobalTheory.Ker.WeakMove

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.FockCompare GlobalTheory.OrientedHeis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem om_dLine (hom : IsWeak ψ S T om) (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (g : GA D S) (h : GA D T)
    {L L' : ℝ →+ WO S T} (hL : IsRealDir T S L) (hL' : IsRealDir T S L') (hLL : ∀ t, L' t = actO S T g h (L t))
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (g, h) (dLine ψ S T L f) = dLine ψ S T L' (om (g, h) f) := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have := i1; have := i2; have := i3; have := i4; have := i5
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have : Countable (ratL T S) := countable_of_Lindelof_of_discrete
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ :=
    (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hKc).1
  have hF : IsThetaFunO ψ S T (om (g, h) f) := hom.om_pres _ _ hf
  have hd : IsThetaFunO ψ S T (dLine ψ S T L f) := theta_dLine hθ hψ hL hf
  have hd' : IsThetaFunO ψ S T (dLine ψ S T L' (om (g, h) f)) := theta_dLine hθ hψ hL' hF
  have hδ : IsThetaFunO ψ S T (om (g, h) (dLine ψ S T L f) - dLine ψ S T L' (om (g, h) f)) :=
    theta_sub (hom.om_pres _ _ hd) hd'
  obtain ⟨C₁, hC₁⟩ := quotient_bound hθ hψ hL hf
  obtain ⟨C₂, hC₂⟩ := quotient_bound hθ hψ hL' hF
  have hν : (μ.restrict 𝓕) Set.univ = 1 := by rw [Measure.restrict_apply_univ]; exact h1
  have h0 : ∫⁻ w, ‖(om (g, h) (dLine ψ S T L f) - dLine ψ S T L' (om (g, h) f)) w‖ₑ ^ 2 ∂(μ.restrict 𝓕) = 0 := by
    refine lintegral_eq_zero_of_approx (μ.restrict 𝓕) hν _ C₁ C₂ fun t ht => ?_
    have hq : IsThetaFunO ψ S T ((t : ℂ)⁻¹ • (heisO ψ S T (L t) f - f)) :=
      theta_smul _ (theta_sub (theta_heisO_real hθ hψ (hL.2 t) hf) hf)
    have hom_q : om (g, h) ((t : ℂ)⁻¹ • (heisO ψ S T (L t) f - f)) =
        (t : ℂ)⁻¹ • (heisO ψ S T (L' t) (om (g, h) f) - om (g, h) f) := by
      rw [map_smul, map_sub, hom.om_heis g h (L t) f hf, ← hLL t]
    refine ⟨om (g, h) (dLine ψ S T L f - (t : ℂ)⁻¹ • (heisO ψ S T (L t) f - f)),
      dLine ψ S T L' (om (g, h) f) - om (g, h) ((t : ℂ)⁻¹ • (heisO ψ S T (L t) f - f)),
      dLine ψ S T L f - (t : ℂ)⁻¹ • (heisO ψ S T (L t) f - f), ?_, ?_, ?_, ?_⟩
    · rw [map_sub]; abel
    · exact hom.om_unit μ 𝓕 hμ h𝓕 _ _ (theta_sub hd hq)
    · intro w
      rw [Pi.sub_apply, norm_sub_rev, ← Pi.sub_apply]
      exact hC₁ t ht w
    · intro w
      rw [hom_q, Pi.sub_apply, norm_sub_rev, ← Pi.sub_apply]
      exact hC₂ t ht w
  exact sub_eq_zero.mp
    (eq_zero_of_lintegral_eq_zero (ratL T S) μ 𝓕 h𝓕 _ hδ.cont (theta_norm_periodic hψ hδ) h0)

theorem om_dRho (hom : IsWeak ψ S T om) (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (g : GA D S) (h : GA D T)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (g, h) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) =
      Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) (om (g, h) f) := by
  rw [dRho_eq_dLine, dRho_eq_dLine]
  exact GlobalTheory.Ker.WeakMove.om_dLine hom hψ hθ g h (isRealDir_lineAt hθ τ z) (isRealDir_lineAt hθ τ _)
    (fun t => lineAt_move hθ g h τ z t) hf

theorem sB_mvB (C : Ctx S T) (g : GA D T) (B : C.Bas) (τ : D.what₂.Tau) :
    C.sB (C.mvB g B) τ * compAt C.θ τ (mt T g) = compAt C.θ τ (mt T g) * C.sB B τ := by
  have h1 : compAt C.θ τ (mt T g) * compAt C.θ τ (mt T g⁻¹) = 1 := compAt_mt_mul_inv τ g
  have h2 : (compAt C.θ τ (mt T g))⁻¹ * compAt C.θ τ (mt T g) = 1 := by
    exact Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_right_inverse h1)
  simp only [Ctx.sB, Ctx.mvB, Matrix.mul_inv_rev, Matrix.mul_assoc, h2, Matrix.mul_one]

theorem isFock_om (C : Ctx S T) (hom : IsWeak C.ψ S T om) (h : GA D S) (g : GA D T) {f : WO S T → ℂ} (hf : C.IsTh f)
    (B : C.Bas) (hB : C.IsFock B f) : C.IsFock (C.mvB g B) (om (h, g) f) := by
  intro τ z
  have hM : compAt C.θ τ (mt T g) * compAt C.θ τ (mt T g⁻¹) = 1 := compAt_mt_mul_inv τ g
  have hG : compAt C.θ τ (mt S h) * compAt C.θ τ (mt S h⁻¹) = 1 := compAt_mt_mul_inv τ h
  obtain ⟨z₀, rfl⟩ : ∃ z₀ : Matrix (Fin T.rank) (Fin S.rank) ℂ, z = compAt C.θ τ (mt T g) * z₀ * compAt C.θ τ (mt S h⁻¹) := by
    refine ⟨compAt C.θ τ (mt T g⁻¹) * z * compAt C.θ τ (mt S h), ?_⟩
    simp only [Matrix.mul_assoc, hG, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hM, Matrix.one_mul]
  have key := hB τ z₀
  have hc : cplxO 1 (C.sB (C.mvB g B) τ) (compAt C.θ τ (mt T g) * z₀ * compAt C.θ τ (mt S h⁻¹)) =
      compAt C.θ τ (mt T g) * cplxO 1 (C.sB B τ) z₀ * compAt C.θ τ (mt S h⁻¹) :=
    cplxO_move hG (by rw [Matrix.one_mul, Matrix.mul_one]) (sB_mvB C g B τ) z₀
  unfold annih at key ⊢
  rw [hc, ← GlobalTheory.Ker.WeakMove.om_dRho hom C.std C.inf h g τ z₀ hf,
    ← GlobalTheory.Ker.WeakMove.om_dRho hom C.std C.inf h g τ _ hf, ← map_smul, ← map_add, key, map_zero]

theorem om_fvec (C : Ctx S T) (hom : IsWeak C.ψ S T om) (h : GA D S) (g : GA D T) {f : WO S T → ℂ} (hf : C.IsTh f)
    (B : C.Bas) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    om (h, g) (C.fvec B f Q) = pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB (C.mvB g B))
      (fun τ => compAt C.θ τ (mt S h)) (C.mvB g B) (om (h, g) f) Q := by
  unfold Ctx.fvec pureTensorO
  refine (pureTensorL_intertwine (IsThetaFunO C.ψ S T) theta_zero (fun a b ha hb => theta_add ha hb)
    (fun c a ha => theta_smul c ha) _ _ (om (h, g)) ?_ f hf Q).2
  intro k f' hf'
  have hG : compAt C.θ k.1 (mt S h) * compAt C.θ k.1 (mt S h⁻¹) = 1 := compAt_mt_mul_inv k.1 h
  have hu : unitMap (compAt C.θ k.1 (mt S h)) (C.mvB g B k.1) k.2.1 k.2.2 =
      compAt C.θ k.1 (mt T g) * unitMap 1 (B k.1) k.2.1 k.2.2 * compAt C.θ k.1 (mt S h⁻¹) := by
    have := unitMap_move (B := 1) (B' := B k.1) (H := compAt C.θ k.1 (mt T g)) hG k.2.1 k.2.2
    rwa [Matrix.mul_one] at this
  have hc : ∀ z, cplxO 1 (C.sB (C.mvB g B) k.1) (compAt C.θ k.1 (mt T g) * z * compAt C.θ k.1 (mt S h⁻¹)) =
      compAt C.θ k.1 (mt T g) * cplxO 1 (C.sB B k.1) z * compAt C.θ k.1 (mt S h⁻¹) := fun z =>
    cplxO_move hG (by rw [Matrix.one_mul, Matrix.mul_one]) (sB_mvB C g B k.1) z
  unfold aPlusAll aPlus crea
  beta_reduce
  refine ⟨?_, ?_⟩
  · exact theta_smul _ (theta_sub (theta_dRho C.inf C.std _ _ hf') (theta_smul _ (theta_dRho C.inf C.std _ _ hf')))
  · simp only [map_smul, map_sub]
    rw [GlobalTheory.Ker.WeakMove.om_dRho hom C.std C.inf h g _ _ hf', GlobalTheory.Ker.WeakMove.om_dRho hom C.std C.inf h g _ _ hf',
      hu]
    exact congrArg _ (congrArg _ (congrArg _
      (congrArg (fun z => Formalism.IndefR.Datum.dRho (heisO C.ψ S T) C.θ k.1 z (om (h, g) f')) (hc _).symm)))

end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem om_move : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → ∀ (h : GA D S) (g : GA D T) f, C.IsTh f → (∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), om (h, g) (dRho (heisO C.ψ S T) C.θ τ z f) = dRho (heisO C.ψ S T) C.θ τ (compAt C.θ τ (mt T g) * z * compAt C.θ τ (mt S h⁻¹)) (om (h, g) f)) ∧ ∀ B, C.IsB B → (C.IsFock B f → C.IsFock (C.mvB g B) (om (h, g) f)) ∧ ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, om (h, g) (C.fvec B f Q) = pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB (C.mvB g B)) (fun τ => compAt C.θ τ (mt S h)) (C.mvB g B) (om (h, g) f) Q := by
  intro D S T C om hom h g f hf
  exact ⟨fun τ z => GlobalTheory.Ker.WeakMove.om_dRho hom C.std C.inf h g τ z hf,
    fun B _ => ⟨fun hB => isFock_om C hom h g hf B hB, fun Q => om_fvec C hom h g hf B Q⟩⟩

end

end GlobalTheory.Ker.WeakMove

end
end
