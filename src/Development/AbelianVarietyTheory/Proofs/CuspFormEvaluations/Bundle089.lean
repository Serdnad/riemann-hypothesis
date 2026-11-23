module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.NormEuclideanEmbeddingEqNetNorm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle007
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle038
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle045
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle034
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle033
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle028
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SumLeFinsumOfSurjectsOntoFinset
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle088
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle070
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle031
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ContDiffOfDifferentiableFd
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.thetaNet_dimension_and_pointCount_bound : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → ∃ (Nt : NetNorms.NetData (recB h.toLawsCore) j ka) (σ₀ : (recB h.toLawsCore).KO →+* ℂ), NetNorms.NetMax Nt ∧ NetNorms.NetLeSup Nt ∧ NetNorms.NetPageG Nt large₂ 1041 3 ∧ NetNorms.NetInj Nt σ₀ ∧ Real.log (Fintype.card (Nt.NN σ₀) : ℝ) ≤ pdR large₂ ka ∧ DeepSubMul (recPJ h j hj) ∧ Real.log (Module.finrank (recB h.toLawsCore).KO ((recB h.toLawsCore).Cusp j ka) : ℝ) ≤ 1041 * Zb D large₂ ^ 3 ∧ ∀ del : ℕ, LatAt (recB h.toLawsCore) j ka → ShareRd (D := D) (j := j) Tn del ((recPJ h j hj).rk ka ((recB h.toLawsCore).Mlat j ka)) → Real.log del ≤ 1041 * Zb D large₂ ^ 3 := by
  exact @GlobalTheory.RunJoin.net_at_run
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem polyDeriv_const_mul_entire {σ W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    (P : MvPolynomial σ ℂ) (u : σ → W) (c : ℂ) {G : W → ℂ} (hG : Differentiable ℂ G) (x : W) :
    I2.polyDeriv P u (fun z => c * G z) x = c * I2.polyDeriv P u G x := by
  have := I2.polyDeriv_sum P u (Finset.univ : Finset Unit) (fun _ => c) (fun _ => G)
    (fun _ _ k => I2.contDiff_of_differentiable_fd hG k) x
  simpa using this

theorem polyDeriv_const_mul_of_entire {σ W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] (P : MvPolynomial σ ℂ) (u : σ → W) (c : ℂ) {T : W → ℂ}
    (hG : Differentiable ℂ fun z => c * T z) (x : W) :
    I2.polyDeriv P u (fun z => c * T z) x = c * I2.polyDeriv P u T x := by
  by_cases hc : c = 0
  · have := polyDeriv_const_mul_entire P u 0 hG x
    simpa [hc] using this
  · have h : T = fun z => c⁻¹ * (c * T z) := by
      funext z; field_simp
    conv_rhs => rw [h]
    rw [polyDeriv_const_mul_entire P u c⁻¹ hG x]
    field_simp

theorem exists_level_translate_jet_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : 𝓞 E, (w : E) + cc (w : E) = 1 → ∀ L : Lt E r, SelfD X L → ∀ x ∈ X.dom, X.IsOrtho x → ∀ t : ℝ, 0 < t → (∀ τ, X.c τ = t) → ∀ (𝔐 : Ideal (𝓞 E)) (M : ℕ), Odd M → 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)} → ∀ v : TF n g, IsVac X bas (w : E) (tens (stdL E n) L) v → ∀ (θ : (Fin g → ℂ) → ℂ) (κ : ℂ), IsTheta1 X bas idx (w : E) x L θ → MeanOne X bas idx x L θ → (∀ z : Fin n → Fin g → ℂ, ∏ b, θ (z b) = κ * thA X bas idx v x z) → ∀ P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n), P ≠ 0 → 3 * P.totalDegree + 2 ≤ M → ∃ y : Matrix (Fin n) (Fin r) E, (∀ b, (M : E) • y b ∈ 𝔐 • L) ∧ ∀ y' : Matrix (Fin n) (Fin r) E, (∀ b, y' b - y b ∈ L) → κ * thP X hr bas idx (heisG X bas y' v) P x ≠ 0 := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn w hw L hL x hd ho t ht hc 𝔐 M hM h𝔐 v hv θ κ hθ hm hκ P hP hdeg
  obtain ⟨F, hF, hFa, hFP⟩ := GlobalTheory.T.exists_theta_sublattice_jet_ne_zero_alt E r X g q0 hr bas idx n hs hn w hw L hL x hd ho t ht hc 𝔐 M hM h𝔐 P hP hdeg
  obtain ⟨s, cf, hs', hsum⟩ := GlobalTheory.T.theta_ideal_lattice_eq_sum_level_translates E r X g q0 hr bas idx n hs hn w hw L hL x hd ho t ht hc 𝔐 M hM h𝔐 v hv
    θ κ hθ hm hκ F hF hFa
  obtain ⟨hcomp, -, -, hdiff, hprod⟩ := fock_laws E r X g bas idx n hs hn x hd 1 θ
  have hprod' := hprod (fun _ => θ) κ v hv.1 hκ
  have hent : ∀ y : Matrix (Fin n) (Fin r) E,
      Differentiable ℂ fun z => κ * thA X bas idx (heisG X bas y v) x z := by
    intro y
    have : (fun z => κ * thA X bas idx (heisG X bas y v) x z) =
        fun z : Fin n → Fin g → ℂ => ∏ b, fock X bas idx x 1 (pv X idx x (y b)) θ (z b) :=
      funext fun z => (hprod' y z).symm
    rw [this]
    have hb : ∀ b, Differentiable ℂ fun z : Fin n → Fin g → ℂ =>
        fock X bas idx x 1 (pv X idx x (y b)) θ (z b) := fun b =>
      (hdiff hθ.1 (pv X idx x (y b))).comp (f := fun z : Fin n → Fin g → ℂ => z b) (differentiable_apply b)
    exact fun z => (HasFDerivAt.finsetProd (u := Finset.univ) fun b _ => (hb b z).hasFDerivAt).differentiableAt
  have hFe : F = fun z => ∑ y ∈ s, cf y * (κ * thA X bas idx (heisG X bas y v) x z) := funext hsum
  rw [hFe, I2.polyDeriv_sum P _ s cf (fun y z => κ * thA X bas idx (heisG X bas y v) x z)
    (fun y _ k => I2.contDiff_of_differentiable_fd (hent y) k)] at hFP
  obtain ⟨y, hy, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hFP
  refine ⟨y, hs' y hy, fun y' hy' => ?_⟩
  have hne' := right_ne_zero_of_mul hne
  have hrow : ∀ b, ∃ c : ℂ, fock X bas idx x 1 (pv X idx x (y b)) θ =
      c • fock X bas idx x 1 (pv X idx x (y' b)) θ := by
    intro b
    have h1 := hθ.2 _ (hy' b)
    have h2 := hcomp (pv X idx x (y b)) (pv X idx x (y' b - y b))
    have h3 : pv X idx x (y b) + pv X idx x (y' b - y b) = pv X idx x (y' b) := by
      funext j
      have := congrFun (per_add X x (y b) (y' b - y b)) (idx j)
      rw [add_sub_cancel] at this
      exact this.symm
    rw [h3] at h2
    have h4 : ∀ (e : ℂ) (a : Fin g → ℂ) (φ : (Fin g → ℂ) → ℂ),
        fock X bas idx x 1 a (e • φ) = e • fock X bas idx x 1 a φ := by
      intro e a φ
      funext z
      simp only [fock, Pi.smul_apply, smul_eq_mul]
      ring
    exact ⟨_, by conv_lhs => rw [← h1, h4, h2, smul_smul]⟩
  choose c hcc using hrow
  have hfun : (fun z => κ * thA X bas idx (heisG X bas y v) x z) =
      fun z => (∏ b, c b) * (κ * thA X bas idx (heisG X bas y' v) x z) := by
    funext z
    rw [← hprod' y z, ← hprod' y' z, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun b _ => by rw [hcc b]; rfl
  rw [hfun, polyDeriv_const_mul_entire P _ _ (hent y'), polyDeriv_const_mul_of_entire P _ _ (hent y')] at hne'
  exact right_ne_zero_of_mul hne'

end GlobalTheory.Dict
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem totalDegree_eq_sum_rows {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ harmA c a n) (h0 : P ≠ 0) (hh : P.IsHomogeneous P.totalDegree) :
    P.totalDegree = ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i) := by
  classical
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.2 h0
  have hr := hP.1.2.2 m hm
  have h1 := hh (MvPolynomial.mem_support_iff.1 hm)
  have h2 : m.degree = P.totalDegree := by rw [Finsupp.degree_eq_weight_one]; exact h1
  rw [← h2, Finsupp.degree_eq_sum]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => hr τ i

theorem lieFac_sq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (x : ℝ) (hx : 0 < x)
    (a : (E →+* ℂ) × ℕ → ℕ) (d : ℕ) (hd : d = ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i)) :
    lieFac Dw x a ^ 2 = ((2 * Real.pi * x)⁻¹) ^ d := by
  have hp : 0 < 2 * Real.pi * x := by positivity
  have hd' : (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), (a (τ, i) : ℝ)) = d := by rw [hd]; push_cast; rfl
  unfold lieFac
  rw [hd', ← Real.exp_nat_mul, ← Real.exp_log (inv_pos.2 hp), ← Real.exp_nat_mul, Real.log_inv]
  congr 1
  push_cast
  ring

theorem i2iAt_of_containsTh : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (xR : ℝ) (nab : NabV Xo c), IsNab Xo c nab → (∀ σ, GoodEmb c σ → IsUnf (U σ) ∧ (∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ((U σ).un k x)) ∧ ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xR) → ∀ α : 𝓞 E, α * H.bar α = (l.M : 𝓞 E) → l.Mb = Ideal.span {H.bar α} → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P₁ : MvPolynomial (LtN Dw n) c.F), Dom a n → P₁ ∈ harmA c a n → _root_.GlobalTheory.BlockTh.IsBlockProd P₁ → ∀ s : c.F, (∀ σ : c.F →+* ℂ, (l.M : ℝ) ^ P₁.totalDegree ≤ ‖σ s‖ ^ 2) → ∀ (N : ℕ) (wR : Fin (N + 1) → Rul Xo c), (∀ i, wR i ∈ sec Xo c a n) → ContainsTh Xo c nab s P₁ wR → ∀ (R0 : ℝ) (m : ℕ), RunOK E r P₁.totalDegree l.M R0 m → (Dw.p ≤ m ∨ Dw.q ≤ m) → ∀ tableLineDegreeFive cc : ℝ, p14 E r n m ≤ tableLineDegreeFive → 8100 * Real.pi * n * (m : ℝ) ^ 4 * (I2.dstar (E := E) m : ℝ) ^ 4 * I2.RR (E := E) / l.M ≤ cc → I2AtFramePoints U xR wR (a, n) (I2.th (E := E) l.M R0) tableLineDegreeFive P₁.totalDegree cc := by
  intro hCI E _ _ _ H Dw l Xo c _ r U xR nab hnab hU α hα hMb a n P₁ hdom hP hbp s hs N wR hw hct R0 m hrun hm
    tableLineDegreeFive cc hP14 hcc σ hσ k x hx
  classical
  obtain ⟨hUn, hFT, hxi⟩ := hU σ hσ
  obtain ⟨b, -, hbd, hbo, -, hphi, hpn⟩ := exists_ortho_frame E r ((U σ).X k) x hx
  obtain ⟨T, Pr, hTr, hq, hPm, hph, hbound⟩ := GlobalTheory.T.unfoldedThetaRule_archimedeanValue_bound hCI E H Dw l Xo c σ r (U σ) k ⟨_, hbd⟩ xR nab hnab hσ hUn
    (hFT k _) hbo (hxi k) α hα hMb a n P₁ hP hbp R0 m hrun hm
  obtain ⟨h0, hh, -⟩ := GlobalTheory.T.determinantBlockProduct_rename_torusPolynomial E H Dw n c.F σ P₁ hbp Dw.mult id (fun _ => le_rfl) Function.injective_id
  have hdeg := totalDegree_eq_sum_rows c a n P₁ hP h0 hh
  have hxR : 0 < xR := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    rw [← hxi k τ]
    exact norm_pos_iff.2 ((map_ne_zero τ).2 ((U σ).X k).ξ0_ne)
  have hM : (0 : ℝ) < l.M := by
    have := Pr.hq
    rw [hq] at this
    exact_mod_cast this
  obtain ⟨jb, hjb, hf⟩ := hct
  choose f hf1 hf2 using hf
  haveI : Finite (LevQ Dw l) := (GlobalTheory.card_levQ E H Dw l).1
  haveI : Fintype (Fin n → LevQ Dw l) := Fintype.ofFinite _
  have hb := hbound f hf1
  rw [finsum_eq_sum_of_fintype] at hb
  have hrec : ∀ j, recNrm (U σ) xR a n (wR j) k x =
      lieFac Dw xR a * ‖rdU (U σ) (wR j) k (FD.rmul x b)‖ := fun j => by
    unfold recNrm
    rw [hpn _ _ (hUn.2.2.2.2.1 a n hdom (wR j) (hw j) k)]
  have hval : ∀ q, rdU (U σ) (wR (jb q)) k (FD.rmul x b) =
      σ s * toC (evR Xo c (f q) ((U σ).un k ⟨_, hbd⟩)) := fun q => by
    have e : wR (jb q) = s • f q := by
      funext p y
      rw [hf2 q p y]
      exact (Algebra.smul_def s (f q p y)).symm
    rw [e, map_smulₛₗ]
    show σ s * rdU (U σ) (f q) k (FD.rmul x b) = _
    congr 1
    exact dif_pos hbd
  have hkey : (Real.pi⁻¹) ^ P₁.totalDegree * Pr.Jbound n ≤ ∑ j, recNrm (U σ) xR a n (wR j) k x ^ 2 := by
    have hl := lieFac_sq Dw xR hxR a _ hdeg
    have hL : (0 : ℝ) ≤ ((2 * Real.pi * xR)⁻¹) ^ P₁.totalDegree := by positivity
    calc (Real.pi⁻¹) ^ P₁.totalDegree * Pr.Jbound n
        = ((2 * Real.pi * xR)⁻¹) ^ P₁.totalDegree * ((l.M : ℝ) ^ P₁.totalDegree *
            ((2 * xR / l.M) ^ P₁.totalDegree * Pr.Jbound n)) := by
          rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← mul_pow, ← mul_pow]
          congr 2
          field_simp
      _ ≤ ((2 * Real.pi * xR)⁻¹) ^ P₁.totalDegree * ((l.M : ℝ) ^ P₁.totalDegree *
            ∑ q, ‖toC (evR Xo c (f q) ((U σ).un k ⟨_, hbd⟩))‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (by positivity)) hL
      _ ≤ ((2 * Real.pi * xR)⁻¹) ^ P₁.totalDegree * (‖σ s‖ ^ 2 *
            ∑ q, ‖toC (evR Xo c (f q) ((U σ).un k ⟨_, hbd⟩))‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hs σ)
            (Finset.sum_nonneg fun _ _ => sq_nonneg _)) hL
      _ = ∑ q, recNrm (U σ) xR a n (wR (jb q)) k x ^ 2 := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [hrec, hval, mul_pow, hl, norm_mul, mul_pow]
      _ = ∑ j ∈ Finset.univ.image jb, recNrm (U σ) xR a n (wR j) k x ^ 2 :=
          (Finset.sum_image (f := fun j => recNrm (U σ) xR a n (wR j) k x ^ 2) fun _ _ _ _ h => hjb h).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
  have hfin := neg_log_sqrt_le_of_jbound E T P₁.totalDegree n Pr _ tableLineDegreeFive cc hkey (by rw [hTr, hPm]; exact hP14)
    (by rw [hPm, hq]; exact hcc)
  rw [hph] at hfin
  rw [← hphi]
  exact hfin

end GlobalTheory.AnVal
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem _root_.GlobalTheory.T.thetaGenerator_pointwise_bound_orthonormal_frame : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → ∀ t : ℝ, 0 < t → (∀ k τ, (U.X k).c τ = t) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ (_ : StarRing (𝓞 E)) (nab : NabV Xo c), IsNab Xo c nab → ∀ (xx : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ f : Rul Xo c, IsThRule Xo c nab xx P f → ∀ k (x : (U.X k).dom), (U.X k).IsOrtho x.1 → ∀ lam : ℝ, 0 < lam → lam ^ 2 ≤ (U.X k).firstMinimumSq x.1 → ‖Formalism.L2.PjFree.toC (evR Xo c f (U.un k x))‖ ≤ (∑ m ∈ P.support, ‖σ (P.coeff m)‖) * (Real.pi * Real.exp 1 * t * (Formalism.L2.Pj.DF Dw a : ℕ)) ^ (((Formalism.L2.Pj.DF Dw a : ℕ) : ℝ) / 2) * Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * (fdeg E * r : ℕ) * n) * (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) / (Real.sqrt Real.pi * lam)) ^ (fdeg E * r * n) := by
  first | exact @GlobalTheory.Dict.ThetaPt.theta_bound_ortho | exact GlobalTheory.Dict.ThetaPt.theta_bound_ortho | (intros; apply GlobalTheory.Dict.ThetaPt.theta_bound_ortho <;> assumption)
end
