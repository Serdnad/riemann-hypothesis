module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle328
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.ConclOfInputs4
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle071
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle072
import Formalism.LocalRingCardinality.Bundle006
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle062
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle244
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.AutSpace GlobalTheory.TypeSum GlobalTheory.TypeSum.GrowthAtPlace Formalism.REAL

namespace GlobalTheory.TypeSum.GKCoef

theorem mem_kFin_iff {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
    {σ : Mx n → (H →L[ℂ] H)} {v : H} : v ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ ↔ IsKFin ε σ v := by
  constructor
  · intro hv
    have : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ ≤ kfin ε σ := sSup_le fun W hW w hw => ⟨W, hW.1, hw, hW.2⟩
    exact this hv
  · rintro ⟨S, h1, h2, h3⟩
    exact (le_sSup (show S ∈ {W : Submodule ℂ H | FiniteDimensional ℂ W ∧ IsKStableOn ε σ W} from ⟨h1, h3⟩)) h2

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {τ : D.what₂.Tau}
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin V.rank → Bool}
  {σ : Mx V.rank → (H →L[ℂ] H)} {P : Mx V.rank} {T : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ →ₗ[ℂ] (GA D V → ℂ)}

theorem map_K (hθ : IsInfFam (D := D) θ) (hP : IsUnit P) (h : Pᴴ * Jm ε * P = gramAt D V τ)
    (hT : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ ε σ P T) {k : Mx V.rank} (hk : k ∈ Kset ε)
    (v w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ) (hw : (w : H) = σ k v) (x : GA D V) {y : Mx V.rank} (hy : y ∈ UJset ε) :
    T w (x * atTau θ V τ (P⁻¹ * y * P)) = T v (x * atTau θ V τ (P⁻¹ * (y * k) * P)) := by
  have hd := (isUnit_iff_isUnit_det _).1 hP
  have hkU := K_le_UJ hk
  have e : P * (P⁻¹ * k * P) * P⁻¹ = k := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  have := hT.mapK (P⁻¹ * k * P) (conj_inv_mem hP h hkU) (by rw [e]; exact hk) v w (by rw [e]; exact hw)
  rw [this, rTr, conj_mul hP, atTau_mul hθ V τ (conj_inv_mem hP h hy) (conj_inv_mem hP h hkU), mul_assoc]

theorem hasDerivAt_map (hθ : IsInfFam (D := D) θ) (hP : IsUnit P) (h : Pᴴ * Jm ε * P = gramAt D V τ)
    (hT : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ ε σ P T) (v w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ) {X : Mx V.rank}
    (hX : X ∈ lieSet ε) (hv : Sm ε σ (v : H)) (hw : (w : H) = dRep σ X v) (x : GA D V) {y : Mx V.rank}
    (hy : y ∈ UJset ε) :
    HasDerivAt (fun t : ℝ => T v (x * atTau θ V τ (P⁻¹ * (y * NormedSpace.exp (t • X)) * P)))
      (T w (x * atTau θ V τ (P⁻¹ * y * P))) 0 := by
  have hd := (isUnit_iff_isUnit_det _).1 hP
  have hX' : P⁻¹ * X * P ∈ lieAt V τ := conj_lie hP h hX
  have e1 : ∀ t : ℝ, P * NormedSpace.exp (t • (P⁻¹ * X * P)) * P⁻¹ = NormedSpace.exp (t • X) := fun t => by
    rw [← conj_exp hP, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  have hder : HasDerivAt (fun t : ℝ => σ (P * NormedSpace.exp (t • (P⁻¹ * X * P)) * P⁻¹) v) w 0 := by
    simp only [e1]; rw [hw]; exact hasDerivAt_dRep (G := Jm ε) hv hX
  have hTw := hT.mapLie _ hX' v w hder
  rw [hTw, Rder]
  have hdiff := differentiable_oneP (hT.aut v).smooth hX' (x * atTau θ V τ (P⁻¹ * y * P)) 0
  refine hdiff.hasDerivAt.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  show T v (x * atTau θ V τ (P⁻¹ * (y * NormedSpace.exp (t • X)) * P)) =
    T v (x * atTau θ V τ (P⁻¹ * y * P) * oneP θ V τ (P⁻¹ * X * P) t)
  rw [conj_mul hP, atTau_mul hθ V τ (conj_inv_mem hP h hy) (conj_inv_mem hP h (exp_mem_UJ hX t)), conj_exp hP,
    ← mul_assoc]
  rfl

end GlobalTheory.TypeSum.GKCoef
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

theorem _root_.GlobalTheory.T.exists_formFamilyHypotheses_changedSecondNorm : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (n : SecNorm B) (G : GlobalFamilyData X ka wL wF) (Gc PH Prw Pet Pd c : ℝ), FamIn large₂ K H Ch Ah Cq Aq C2 A2 CR S Tn G Gc PH Prw Pet Pd → PtIn S Tn G c Gc PH Prw Pet nus → ∃ G' : GlobalFamilyData (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X) ka wL wF, FamIn large₂ K H Ch Ah Cq Aq C2 A2 CR (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S) Tn G' Gc PH Prw Pet Pd ∧ PtIn (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S) Tn G' c Gc PH Prw Pet nus := by
  first | exact @GlobalTheory.NormMove.exists_famIn_ptIn | exact GlobalTheory.NormMove.exists_famIn_ptIn | (intros; apply GlobalTheory.NormMove.exists_famIn_ptIn <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

theorem _root_.GlobalTheory.T.indexBoundIntrinsicHypotheses_netBound_degreeTwo : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (CL : ℝ) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ), InputsR large₂ X (kR CL) H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus → InputsR large₂ X (k4 large₂ CL) H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus := by
  first | exact @GlobalTheory.FinalJoin.inputsR_deg_two | exact GlobalTheory.FinalJoin.inputsR_deg_two | (intros; apply GlobalTheory.FinalJoin.inputsR_deg_two <;> assumption)
end

section

set_option autoImplicit false

namespace GlobalTheory.FinalJoin

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

theorem pageOK_of_pageRun_beyond : ∀ Z₀ : ℝ → ℝ → ℝ, ∃ x₀ : ℝ → ℝ → ℝ, ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), InR D j → PageRun large₂ X H C2 A2 CT ka wL wF Tn nP nW h0 → x₀ H.CA H.CK ≤ large₂.sc.x → PageOK large₂ X H C2 A2 CT ka wL wF Tn nP nW h0 ∧ Z₀ H.CA H.CK ≤ zBase large₂ := by
  intro Z₀
  refine ⟨fun a b => max (Z₀ a b) (4 * b), ?_⟩
  intro D B P j X large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hj hP hx
  have hx1 : Z₀ H.CA H.CK ≤ large₂.sc.x := (le_max_left _ _).trans hx
  have hx2 : 4 * H.CK ≤ large₂.sc.x := (le_max_right _ _).trans hx
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hd⟩ := hP.hyp.2.1
  rw [hP.tie.1] at hd
  have hA : 12 ≤ A2 := hP.tie.2.2.2.2.2
  have hC : 1000 ≤ C2 := hd.1
  have hL : 1 ≤ large₂.sc.L := by
    unfold Scale.L; exact Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hfr : (D.R.f : ℝ) * D.R.r ≤ zBase large₂ := by
    unfold zBase
    exact le_mul_of_one_le_right (by positivity) hL
  have hxZ : large₂.sc.x ≤ zBase large₂ := hP.hyp.1.1.trans hfr
  have hZ1 : 1 ≤ zBase large₂ := WeightFamilies.one_le_zBase large₂
  have hZP : zBase large₂ ≤ WeightFamilies.PPv D large₂ C2 A2 := by
    unfold WeightFamilies.PPv
    have h1 : zBase large₂ ≤ zBase large₂ ^ A2 := by
      calc zBase large₂ = zBase large₂ ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ zBase large₂ ^ A2 := Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
    exact h1.trans (le_mul_of_one_le_left (by linarith) (by linarith))
  have hf8 : (8 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast D.eight_le_f
  have hP1 : 1 ≤ WeightFamilies.PPv D large₂ C2 A2 := hZ1.trans hZP
  have hPP : WeightFamilies.PPv D large₂ C2 A2 ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 * D.R.f := by
    have h1 : WeightFamilies.PPv D large₂ C2 A2 ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 := by nlinarith
    exact h1.trans (le_mul_of_one_le_right (by positivity) (by linarith))
  have hfrd := pageRun_sq_le_rd_and_eight_le_rank D B P j X large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hj hP
  exact ⟨⟨hP.hyp, hP.page, hP.tie, indexBoundConstant_le_pagePolynomial_of_runConditions D B P j X large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hj hP,
    hfrd.1, hfrd.2, three_le_DF_of_pageRun D B P j X large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hj hP,
    hx2.trans (hxZ.trans (hZP.trans hPP))⟩, hx1.trans hxZ⟩

end GlobalTheory.FinalJoin
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

theorem _root_.GlobalTheory.T.indexBoundChosenFamily_of_intrinsicHypotheses : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (X : WeightAlgebra.Prov D B P) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ), InputsR large₂ (X j h1 h2) K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus → TieC K H Ch Ah Cq Aq C2 A2 CR → PageAt large₂ C2 A2 → PageSupp D large₂ B C2 A2 nW S wL → Inputs4 large₂ (X j h1 h2) K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus := by
  first | exact @GlobalTheory.FinalJoin.inputs4_of_inputsR | exact GlobalTheory.FinalJoin.inputs4_of_inputsR | (intros; apply GlobalTheory.FinalJoin.inputs4_of_inputsR <;> assumption)
end

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

namespace GlobalTheory.TypeSum.TraceBound

theorem trace_bound : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∃ (d : ℕ) (X : Fin d → Mx n), (∀ i, X i ∈ lieSet ε ∧ (X i)ᴴ = -X i ∧ hs (X i) ≤ 1) ∧ ∀ S : List (List (Mx n)), Words (lieSet ε) S → ∃ (r : ℕ) (A : ℝ), ∀ (q : ℕ) (e : Fin q → H) (μ : Fin q → ℝ), Orthonormal ℂ e → (∀ i, IsKFin ε σ (e i)) → (∀ i, 1 ≤ μ i) → (∀ i, onePlusCas σ X (e i) = (μ i : ℂ) • e i) → ∑ i, sobNorm σ S (e i) ^ 2 / μ i ^ r ≤ A := by
  intro n ε H _ _ _ σ hσ
  obtain ⟨hk, hp⟩ := GlobalTheory.T.indefinite_unitary_lie_orthonormal_bases_props n ε
  obtain ⟨χ, hχ⟩ := GlobalTheory.T.casimir_unitaryGroup_acts_by_scalar_smoothVectors n ε H σ hσ
  refine ⟨_, kB ε, hk, fun S hS => ?_⟩
  obtain ⟨S0, C0, hS0, hC0, HS⟩ := SobHS.sobolev_hilbertSchmidt n ε H σ hσ
  have hT : Words (lieSet ε) (S.flatMap fun l => S0.map (· ++ l)) := by
    intro m hm X hX
    obtain ⟨l, hl, hm⟩ := List.mem_flatMap.1 hm
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hm
    exact (List.mem_append.1 hX).elim (hS0 l' hl' X) (hS l hl X)
  obtain ⟨s, C, hC⟩ := GlobalTheory.T.words_on_weighted_casimir_eigenvectors_bounded_frame n ε H σ hσ (fun i => (hk i).1) (fun b => (hp b).1) χ hχ (GlobalTheory.T.elliptic_estimate_word_le_onePlusLaplacian_pow n ε H σ hσ) _ hT
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  refine ⟨2 * s, S.length * (S.length * (C0 * C')), fun q e μ he hK hμ heig => ?_⟩
  have hsm : ∀ j, Sm ε σ (e j) := fun j => hσ.2.2.1 _ (hK j)
  have hμ0 : ∀ j, 0 < μ j := fun j => lt_of_lt_of_le one_pos (hμ j)

  have key : ∀ l ∈ S, ∑ j, ‖Dw σ l (e j)‖ ^ 2 / μ j ^ (2 * s) ≤ C0 * C' := by
    intro l hl
    have hlw : ∀ X ∈ l, X ∈ lieSet ε := hS l hl
    set c : Fin q → ℝ := fun j => (μ j ^ s)⁻¹ with hc
    have hc0 : ∀ j, 0 ≤ c j := fun j => inv_nonneg.2 (pow_nonneg (hμ0 j).le _)
    set x : Fin q → H := fun j => ((c j : ℝ) : ℂ) • Dw σ l (e j) with hx
    have hxs : ∀ j, Sm ε σ (x j) := fun j =>
      sm_iff.2 ((smooth (Jm ε) σ).smul_mem _ (sm_iff.1 ((hsm j).word hσ.1 hlw)))
    have hframe : ∀ l' ∈ S0, ∀ z : Fin q → ℂ, ‖∑ j, z j • Dw σ l' (x j)‖ ^ 2 ≤ C' * ∑ j, ‖z j‖ ^ 2 := by
      intro l' hl' z
      have e1 : ∀ j, z j • Dw σ l' (x j) = (((c j : ℝ) : ℂ) * z j) • Dw σ (l' ++ l) (e j) := fun j => by
        rw [hx, Dw_smul hσ.1 (hS0 l' hl') _ ((hsm j).word hσ.1 hlw), Dw_append, smul_smul, mul_comm]
      simp only [e1]
      have hm : l' ++ l ∈ S.flatMap fun l => S0.map (· ++ l) :=
        List.mem_flatMap.2 ⟨l, hl, List.mem_map.2 ⟨l', hl', rfl⟩⟩
      refine (hC _ hm q e μ he hK hμ heig z).trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Finset.sum_nonneg fun _ _ => by positivity)
    have hH := HS (Fin q) x x C' hC'0 hxs hframe
    have eQ : ∑ j, ⟪x j, x j⟫_ℂ = ((∑ j, ‖x j‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun j _ => inner_self_eq_norm_sq_to_K (x j)
    rw [eQ, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hH
    have hQ0 : 0 ≤ ∑ j, ‖x j‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    have hQ : ∑ j, ‖x j‖ ^ 2 ≤ C0 * C' := by
      by_contra hne
      push_neg at hne
      have hK0 : 0 ≤ C0 * C' := mul_nonneg hC0 hC'0
      nlinarith
    refine le_of_eq_of_le (Finset.sum_congr rfl fun j _ => ?_) hQ
    rw [hx]
    simp only
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc0 j), mul_pow, hc, inv_pow, ← pow_mul,
      mul_comm s 2, div_eq_mul_inv, mul_comm]

  have hcs : ∀ j, sobNorm σ S (e j) ^ 2 ≤ S.length * ∑ i : Fin S.length, ‖Dw σ S[i] (e j)‖ ^ 2 := by
    intro j
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin S.length)))
      (f := fun i => ‖Dw σ S[i] (e j)‖)
    rw [Finset.card_univ, Fintype.card_fin] at this
    unfold sobNorm
    rw [← Fin.sum_univ_fun_getElem]
    exact this
  calc ∑ j, sobNorm σ S (e j) ^ 2 / μ j ^ (2 * s)
      ≤ ∑ j, (S.length * ∑ i : Fin S.length, ‖Dw σ S[i] (e j)‖ ^ 2) / μ j ^ (2 * s) :=
        Finset.sum_le_sum fun j _ => div_le_div_of_nonneg_right (hcs j) (pow_nonneg (hμ0 j).le _)
    _ = S.length * ∑ i : Fin S.length, ∑ j, ‖Dw σ S[i] (e j)‖ ^ 2 / μ j ^ (2 * s) := by
        simp only [Finset.mul_sum, Finset.sum_div, mul_div_assoc]
        exact Finset.sum_comm
    _ ≤ S.length * ∑ _i : Fin S.length, C0 * C' := by
        gcongr with i
        exact key _ (List.getElem_mem _)
    _ = S.length * (S.length * (C0 * C')) := by simp

end GlobalTheory.TypeSum.TraceBound
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos

theorem GlobalTheory.TypeSum.CoefClos.coefSum_cSm_wordF : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ (d : ℕ) (L : Fin d → (H →ₗ[ℂ] ℂ)), (∀ a, Sobolev₂ (lieSet ε) σ (L a)) →
    ∀ x : Fin d → H, (∀ a, Sm ε σ (x a)) →
    CSm ε (fun y => ∑ a, L a (σ y (x a))) ∧ ∀ (u : List (Ltr ε)), ∀ y ∈ UJset ε,
      wordF u (fun y => ∑ a, L a (σ y (x a))) y = ∑ a, L a (σ y (wordV σ u (x a))) := by
  intro n ε H _ _ _ σ h d L hL x hx
  have hd : ∀ (v : Fin d → H), (∀ a, Sm ε σ (v a)) → ∀ X ∈ lieSet ε, ∀ y ∈ UJset ε,
      HasDerivAt (fun t : ℝ => ∑ a, L a (σ (y * NormedSpace.exp (t • X)) (v a)))
        (∑ a, L a (σ y (dRep σ X (v a)))) 0 := by
    intro v hv X hX y hy
    refine HasDerivAt.fun_sum fun a _ => ?_
    simpa using CoefLow.hasDerivAt_coef h (hL a) (hv a) hX hy 0
  have hw : ∀ (u : List (Ltr ε)) (a : Fin d), Sm ε σ (wordV σ u (x a)) := by
    intro u a
    induction u with
    | nil => exact hx a
    | cons z u ih =>
      rcases z with X | k
      · exact Sm.word h.1 ih (l := [X.1]) (by simpa using X.2)
      · exact Sm.translate h.1 ih (K_le_UJ k.2)
  refine ⟨⟨fun l y => ∑ a, L a (σ y (Dw σ l (x a))), fun _ _ => rfl, fun l hl X hX g hg => ?_, fun l hl => ?_⟩,
    fun u => ?_⟩
  · exact hd _ (fun a => Sm.word h.1 (hx a) hl) X hX g hg
  · exact continuousOn_finsetSum _ fun a _ => h.continuousOn_coef (hL a) (Sm.word h.1 (hx a) hl)
  · induction u with
    | nil => exact fun _ _ => rfl
    | cons z u ih =>
      intro y hy
      rcases z with X | k
      · have e : (fun t : ℝ => wordF u (fun y => ∑ a, L a (σ y (x a))) (y * NormedSpace.exp (t • X.1))) =
            fun t : ℝ => ∑ a, L a (σ (y * NormedSpace.exp (t • X.1)) (wordV σ u (x a))) :=
          funext fun t => ih _ (mul_mem_UJ hy (exp_mem_UJ X.2 t))
        exact (congrArg (fun f => deriv f 0) e).trans (hd _ (hw u) X.1 X.2 y hy).deriv
      · refine (ih _ (mul_mem_UJ hy (K_le_UJ k.2))).trans (Finset.sum_congr rfl fun a _ => ?_)
        rw [sigma_mul h.1 hy (K_le_UJ k.2)]
        rfl
end
