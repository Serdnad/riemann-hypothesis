module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle184
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle262
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle043
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle318
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle300
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle270
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle037
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle299
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle166
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle060
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsArchimedeanAdeleChartOfRealChart
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle079
public import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle320
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle322
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle225
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle321
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle291
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntertwinerSelfDualVacuumIsVacuum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPullbackConstantSqEqDet
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryThetaConstantEqInverseDeterminantPhase
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

namespace GlobalTheory.ThetaConj

theorem U_pullB_eq_prod (D : D7) (hG : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hb : OnB D b) (g : ℂ → ℂ) (t z : VC D N N') :
    U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b g) z =
      ∏ j, U1 (lamOf D cc δ) (coordB D (tor0 D cc δ) b j t) g (coordB D (tor0 D cc δ) b j z) := by
  obtain ⟨-, -, hP, -, -⟩ := GlobalTheory.OnCoord.coords_of_orthonormal_basis D hG cc δ N N' r b hb
  unfold U U1 pullB Hf
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, hP, hP]
  congr 1
  · exact Finset.prod_congr rfl fun j _ => by rw [coordB_add]
  · congr 1
    simp only [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [tor0]
    ring

theorem normalisedThetaPullback_mem_torsionTranslatesSpan (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ) (t0 : ℂ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (N N' r : ℕ)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hb : OnB D b) :
    pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0) ∈ Tr D (tor0 D cc δ) b := by
  have hG : admG1 D := (GlobalTheory.InducedType.induced_type D).1
  have hgood := isTraceCompatibleTorusEmbedding_standardTorus D hG cc δ
  obtain ⟨-, -, -, hL, -⟩ := GlobalTheory.OnCoord.coords_of_orthonormal_basis D hG cc δ N N' r b hb
  set t : VC D N N' := ∑ j, (fun _ : Fin r => t0) j • embV D (tor0 D cc δ) (b j) with htdef
  have hco : ∀ j, coordB D (tor0 D cc δ) b j t = t0 := fun j => hgood.coordB_sum hb.1 _ j
  have h2 : (2 : ℕ) • t ∈ LaB D (tor0 D cc δ) b := by
    rw [hL]
    intro k
    rw [two_nsmul, coordB_add, hco, ← two_mul]
    exact ht.1
  have hq : U1 (lamOf D cc δ) t0 (sgStar (lamOf D cc δ)) 0 ∈ Qbar := by
    have := (GlobalTheory.T.forall_use1 D cc δ hc).1 t0 ⟨2, two_pos, by exact_mod_cast ht.1⟩ 0
    simpa [coef1] using this
  have hmem : U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) ∈
      Tr D (tor0 D cc δ) b := Submodule.subset_span ⟨t, ⟨2, two_pos, h2⟩, rfl⟩
  have := Submodule.smul_mem _
    (⟨(U1 (lamOf D cc δ) t0 (sgStar (lamOf D cc δ)) 0)⁻¹ ^ r, pow_mem (inv_mem hq) r⟩ : Qbar) hmem
  convert this using 1
  funext z
  change _ = (U1 (lamOf D cc δ) t0 (sgStar (lamOf D cc δ)) 0)⁻¹ ^ r *
    U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) z
  rw [U_pullB_eq_prod D hG cc δ b hb]
  simp only [hco, pullB, GL3Theta.th0, div_eq_inv_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

end GlobalTheory.ThetaConj
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem chapterM_theta : ∀ (N r : ℕ) (χ : DirichletCharacter ℂ N) (sg : ℂ), 0 < N → r.Prime → 7 ≤ r → r ∣ N →
    (sg = 1 ∨ sg = -1) → ∃ θ : DirichletCharacter ℂ N, θ (-1) = sg ∧ θ * χ ≠ 1 ∧ θ * χ⁻¹ ≠ 1 := GlobalTheory.T.exists_dirichletCharacter_parity_mul_ne_one_mul_inv_ne_one

theorem chapterM_smooth : ∀ (N l e : ℕ) (θ₁ θ₂ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l), 0 < N → l.Prime →
    ¬ l ∣ N → 1 ≤ e → θ₁ ≠ 1 → θ₂ ≠ 1 → ∃ c d : ℕ, 1 < c ∧ 1 < d ∧ c.Coprime (6 * N * l) ∧ d.Coprime (6 * N * l) ∧
      (∀ z : ℂ, ‖z‖ = 1 → (c : ℂ) ^ e ≠ z) ∧ ∀ n₁ n₂ : ℤ, (n₁ = 1 ∨ n₁ = -1) →
        (d : ℂ) ^ 2 ≠ (d : ℂ) ^ (e + 1) * (θ₁ d ^ n₁ * ψ d ^ n₂) ∧ (d : ℂ) ^ 2 ≠ (d : ℂ) ^ (e + 1) * (θ₂ d ^ n₁ * ψ d ^ n₂) := GlobalTheory.T.exists_smoothing_integers_coprime

theorem norm_symm_char_unit {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) {N : ℕ} [NeZero N]
    (φ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) : ‖ι.symm (φ u)‖ = 1 := by
  have h : (φ u) ^ Fintype.card (ZMod N)ˣ = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
  have h2 : ‖ι.symm (φ u)‖ ^ Fintype.card (ZMod N)ˣ = 1 := by
    rw [← norm_pow, ← map_pow, h, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) Fintype.card_ne_zero).1 h2

theorem chapterM_of_level (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (e : ℕ) (he : 1 ≤ e)
    (g : Newform (2 * e + 1)) (hal : ‖ι.symm (g.a l)‖ = 1) (ψ : DirichletCharacter ℂ l)
    (N r : ℕ) (hN : 0 < N) (hr : r.Prime) (hr7 : 7 ≤ r) (hrN : r ∣ N) (hlN : ¬ l ∣ N)
    (χ : DirichletCharacter ℂ N) (g' : ℕ → ℂ) (hprim : Prim (2 * e + 1) N χ g')
    (hg' : ∀ n : ℕ, n.Coprime N → g' n = g.a n) :
    ∃ (θ : DirichletCharacter ℂ N) (α v : ℂ) (B : ℕ) (c : ℕ → ℂ) (c₁ d₁ : ℕ),
      5 ≤ N ∧ ‖ι.symm α‖ = 1 ∧
      α ^ 2 - g.a l * α + χ l * (l : ℂ) ^ (2 * e) = 0 ∧
      EigAll (2 * e + 1) N l χ (fun q => g.a q) α B c ∧ χ (-1) = -1 ∧ θ (-1) = (-1) ^ e * ψ (-1) ∧
      MeasMu ι e ((-1) ^ e * ψ (-1)) (hat θ) (tw2 N ((-1) ^ e * ψ (-1))) ψ α B c v ∧ v ≠ 0 ∧
      1 < c₁ ∧ 1 < d₁ ∧ c₁.Coprime (6 * N * l) ∧ d₁.Coprime (6 * N * l) ∧
      (∀ z : ℂ, ‖z‖ = 1 → (c₁ : ℂ) ^ e ≠ z) ∧ ∀ n₁ n₂ : ℤ, (n₁ = 1 ∨ n₁ = -1) →
        (d₁ : ℂ) ^ 2 ≠ (d₁ : ℂ) ^ (e + 1) * ((θ * χ) d₁ ^ n₁ * ψ d₁ ^ n₂) ∧
        (d₁ : ℂ) ^ 2 ≠ (d₁ : ℂ) ^ (e + 1) * ((θ * χ⁻¹) d₁ ^ n₁ * ψ d₁ ^ n₂) := by
  have hlp : l.Prime := Fact.out
  haveI : NeZero N := ⟨hN.ne'⟩
  have hcop : l.Coprime N := (Nat.Prime.coprime_iff_not_dvd hlp).2 hlN
  have hgl : g' l = g.a l := hg' l hcop

  have hχm1 : χ (-1) = -1 :=
    (GlobalTheory.T.odd_chi_and_tendsto_twisted_LSeries_ne_zero_of_prim (2 * e + 1) N 1 χ (1 : DirichletCharacter ℂ 1) g' ((((2 * e + 1 : ℕ) : ℝ) + 1) / 2)
      (odd_two_mul_add_one e) hN one_pos hprim le_rfl).1

  have hψ : ψ (-1) = 1 ∨ ψ (-1) = -1 :=
    mul_self_eq_one_iff.mp (by rw [← map_mul, neg_one_mul, neg_neg, map_one])
  have hsg : (-1 : ℂ) ^ e * ψ (-1) = 1 ∨ (-1 : ℂ) ^ e * ψ (-1) = -1 := by
    rcases neg_one_pow_eq_or ℂ e with h | h <;> rcases hψ with h' | h' <;> simp [h, h']
  obtain ⟨θ, hθm1, hθχ, hθχ'⟩ := chapterM_theta N r χ _ hN hr hr7 hrN hsg

  set u : (ZMod N)ˣ := ZMod.unitOfCoprime l hcop with hu
  have hul : ((u : ZMod N)) = (l : ZMod N) := ZMod.coe_unitOfCoprime l hcop
  have hnχ : ‖ι.symm (χ l)‖ = 1 := by rw [← hul]; exact norm_symm_char_unit ι χ u
  have hnχ' : ‖ι.symm (χ⁻¹ l)‖ = 1 := by rw [← hul]; exact norm_symm_char_unit ι χ⁻¹ u
  have hnl : ‖ι.symm (l : ℂ)‖ < 1 := by
    rw [map_natCast, ← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hlp.one_lt)
  have ht : ‖ι.symm (χ⁻¹ l * g' l)‖ = 1 := by rw [map_mul, norm_mul, hnχ', hgl, hal, one_mul]
  have hD : ‖ι.symm (χ⁻¹ l * (l : ℂ) ^ (2 * e))‖ < 1 := by
    rw [map_mul, norm_mul, hnχ', one_mul, map_pow, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hnl (by omega)
  obtain ⟨α, β, hs, hp, hα, -⟩ := GlobalTheory.unitRoot_split l ι _ _ ht hD

  obtain ⟨B, c, hEig, hval⟩ := GlobalTheory.T.exists_heckeEigenfunctional_depletedEisenstein_ne_zero l ι e N χ θ ψ g' α β he hN hlN hprim hs hp hα hθm1 hθχ

  obtain ⟨x, y, hxy⟩ : IsCoprime (N : ℤ) (l : ℤ) := Nat.isCoprime_iff_coprime.2 hcop.symm
  have hbez : (N : ℤ) * x * 1 - l * (-y) * 1 = 1 := by linear_combination hxy
  obtain ⟨B', c', hall, hrel⟩ := GlobalTheory.T.eigenfunctionalAllCharacters_of_atkinLehner (2 * e + 1) N l χ g' α B c x (-y) 1 1 hbez (by omega) hN hlp hlN hEig
  have hα0 : α ≠ 0 := by
    intro h; rw [h, map_zero, norm_zero] at hα; exact zero_ne_one hα
  have key := GlobalTheory.T.muModelProduct_value_ne_zero_of_depleted e N l χ⁻¹ θ ψ (fun n => conj (g' n)) α β x (-y) 1 1 hbez he hN hlp hlN
  simp only [inv_inv, Complex.conj_conj] at key
  have hv := key hprim hs hp hα0 hθm1 hθχ B c hEig hval B' c' hrel (fun a ha => hall.U a ha)
  have hmeas := GlobalTheory.T.exists_muModel_measure_of_eigenfunctional l ι e N χ θ ψ (χ l * α) B' c' he hN hlN
    (by rw [map_mul, norm_mul, hnχ, hα, one_mul]) hall.kill hall.U hθm1 hχm1
  obtain ⟨c₁, d₁, hc1, hd1, hc1c, hd1c, hc, hd⟩ := chapterM_smooth N l e (θ * χ) (θ * χ⁻¹) ψ hN hlp hlN he hθχ hθχ'
  refine ⟨θ, χ l * α, _, B', c', c₁, d₁, ?_, ?_, ?_, ?_, hχm1, hθm1, hmeas, ?_, hc1, hd1, hc1c, hd1c, hc, hd⟩
  · have := Nat.le_of_dvd hN hrN; omega
  · rw [map_mul, norm_mul, hnχ, hα, one_mul]
  · have hxy1 : χ l * χ⁻¹ l = 1 := by
      rw [← hul, MulChar.inv_apply_eq_inv', mul_inv_cancel₀]
      exact (u.isUnit.map χ).ne_zero
    rw [hgl] at hs
    linear_combination ((χ l) ^ 2 * α) * hs - (χ l) ^ 2 * hp + (χ l * g.a l * α - χ l * (l : ℂ) ^ (2 * e)) * hxy1
  · refine ⟨⟨fun a ha q hq hqN => ?_, hall.U⟩, hall.kill⟩
    have hqc : q.Coprime N := (Nat.Prime.coprime_iff_not_dvd hq).2 (fun h => hqN (h.trans (dvd_mul_right N l)))
    rw [← hg' q hqc]
    exact hall.T a ha q hq hqN
  · refine mul_ne_zero (div_ne_zero two_ne_zero ?_) hv
    exact_mod_cast (Nat.totient_pos.2 hN).ne'

theorem chapterM_holds : CuspidalUnitaryTwistsClaim := by
  intro l _ hl2 ι e he g hlM hal ψ N₀ hN₀ hlN₀
  have hlp : l.Prime := Fact.out
  obtain ⟨r, hrge, hr⟩ := Nat.exists_infinite_primes (l + 7)
  have hrl : ¬ l ∣ r := by
    intro h
    rcases (Nat.dvd_prime hr).1 h with h1 | h1
    · exact hlp.one_lt.ne' h1
    · omega
  obtain ⟨χ, hprim, hχ⟩ := depleted_newform_prim (2 * e + 1) (N₀ * r) g (by omega) (by nlinarith [hr.two_le])
  have hMpos := g.pos
  have hrpos := hr.pos
  have hN : 0 < g.M * (g.M * (N₀ * r)) ^ 2 := by positivity
  have hL : g.M * (N₀ * r) ∣ g.M * (g.M * (N₀ * r)) ^ 2 := (dvd_pow_self _ two_ne_zero).mul_left g.M
  have hrN : r ∣ g.M * (g.M * (N₀ * r)) ^ 2 := (dvd_mul_of_dvd_right (dvd_mul_left r N₀) g.M).trans hL
  have hN₀N : N₀ ∣ g.M * (g.M * (N₀ * r)) ^ 2 := (dvd_mul_of_dvd_right (dvd_mul_right N₀ r) g.M).trans hL
  have hMN : g.M ∣ g.M * (g.M * (N₀ * r)) ^ 2 := dvd_mul_right _ _
  have hlN : ¬ l ∣ g.M * (g.M * (N₀ * r)) ^ 2 := by
    intro h
    rcases hlp.dvd_mul.1 h with h | h
    · exact hlM h
    · rcases hlp.dvd_mul.1 (hlp.dvd_of_dvd_pow h) with h | h
      · exact hlM h
      · rcases hlp.dvd_mul.1 h with h | h
        · exact hlN₀ h
        · exact hrl h
  have hg' : ∀ n : ℕ, n.Coprime (g.M * (g.M * (N₀ * r)) ^ 2) →
      (fun n => if n.Coprime (g.M * (N₀ * r)) then g.a n else 0) n = g.a n := by
    intro n hn
    simp only [if_pos (hn.coprime_dvd_right hL)]
  obtain ⟨θ, α, v, B, c, c₁, d₁, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ :=
    chapterM_of_level l ι e he g hal ψ _ r hN hr (by omega) hrN hlN χ _ hprim hg'
  exact ⟨_, χ, θ, α, v, B, c, c₁, d₁, h1, hMN, hN₀N, hlN, hχ, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

end GlobalTheory.EisM

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeFinTrivial

theorem mem_closure_range {F E ι : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (τ : ι → E →+* ℂ) (θ : ι → (InfiniteAdeleRing F ⊗[F] E →+* ℂ))
    (h1 : ∀ i (x : E), θ i ((1 : InfiniteAdeleRing F) ⊗ₜ[F] x) = τ i x)
    (h2 : ∀ i, Continuous fun a : InfiniteAdeleRing F => θ i (a ⊗ₜ[F] (1 : E)))
    (y : InfiniteAdeleRing F ⊗[F] E) :
    (fun i => θ i y) ∈ closure (Set.range fun (k : E) i => τ i k) := by
  let S : AddSubgroup (ι → ℂ) := (RingHom.pi τ).toAddMonoidHom.range.topologicalClosure
  show (fun i => θ i y) ∈ S
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact S.zero_mem
  | add a b ha hb => simp only [map_add (f := _)]; exact S.add_mem ha hb
  | tmul a x =>
    have e : ∀ (a : InfiniteAdeleRing F) i, θ i (a ⊗ₜ[F] x) = θ i (a ⊗ₜ[F] (1 : E)) * τ i x := by
      intro a i
      rw [← h1, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have hc : Continuous fun (a : InfiniteAdeleRing F) i => θ i (a ⊗ₜ[F] x) := by
      refine continuous_pi fun i => ?_
      simp only [e]
      exact (h2 i).mul continuous_const
    refine DenseRange.induction_on (InfiniteAdeleRing.denseRange_algebraMap F) a
      (isClosed_closure.preimage hc) fun f => ?_
    refine subset_closure ⟨f • x, funext fun i => ?_⟩
    show τ i (f • x) = θ i (algebraMap F _ f ⊗ₜ[F] x)
    rw [← h1, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem denseRange_units {E ι : Type} [Field E] [Finite ι] [Nonempty ι] (τ : ι → E →+* ℂ)
    (h : DenseRange fun (k : E) i => τ i k) :
    DenseRange fun (k : Eˣ) i => Units.map (τ i).toMonoidHom k := by
  have hg : Topology.IsOpenEmbedding (Pi.map (fun _ : ι => (Units.val : ℂˣ → ℂ))) :=
    Topology.IsOpenEmbedding.piMap (fun w => Units.isOpenEmbedding_val)
  rw [DenseRange, dense_iff_inter_open]
  rintro U hU ⟨u, hu⟩
  obtain ⟨k, v, hv, hk⟩ := h.exists_mem_open (hg.isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    obtain ⟨w⟩ : Nonempty ι := inferInstance
    have h1 := congrFun hk w
    beta_reduce at h1
    rw [map_zero] at h1
    exact (v w).ne_zero h1
  refine ⟨v, hv, Units.mk0 k hk0, ?_⟩
  funext w
  exact Units.ext (congrFun hk w).symm



open GlobalTheory.FockCompare in
theorem eq_one_of_trivial_on_finite : ∀ (D : D7) (c : (AE D)ˣ →* Circle), IsHeckeChar D c → (∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → c x = 1) → ∀ x, c x = 1 := by
  intro D c hc hf
  obtain ⟨⟨θ', hθ'⟩, -⟩ := GlobalTheory.Member.infiniteAdele_bijective D
  let θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) := fun τ => θ' (tauE D τ)
  have hθ : IsInfFam θ := fun τ => hθ' _
  obtain ⟨ρ, hρ, r1, r0⟩ := exists_real_chart D θ hθ (GlobalTheory.CMTypePlaces.places_bijective D)
  obtain ⟨s, hs⟩ := RealChart.exists_chart D θ hθ ρ hρ r1 r0
  obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
  haveI : Nonempty D.what₂.Tau :=
    ⟨((GlobalTheory.CMTypePlaces.places_bijective D).2 (Classical.arbitrary _)).choose⟩
  have ext : ∀ a b : AE D, finPart D a = finPart D b → (∀ τ, θ τ (infPart D a) = θ τ (infPart D b)) → a = b := by
    intro a b h1 h2
    rw [← sub_eq_zero]
    exact hs.ext _ (by rw [RingHom.map_sub, h1, sub_self]) fun τ => by
      rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self]
  let t : (D.what₂.Tau → ℂˣ) → AE D := fun z => s (fun τ => (z τ : ℂ)) + (1 - s 1)
  have tf : ∀ z, finPart D (t z) = 1 := fun z => by
    simp only [t, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, hs.fin, zero_add, sub_zero]
  have ti : ∀ z τ, θ τ (infPart D (t z)) = z τ := fun z τ => by
    simp only [t, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, hs.comp, Pi.one_apply, sub_self, add_zero]
  have tc : Continuous t :=
    (hs.cont.comp (continuous_pi fun τ => Units.continuous_val.comp (continuous_apply τ))).add continuous_const
  let T : (D.what₂.Tau → ℂˣ) →* AE D :=
    { toFun := t
      map_one' := ext _ _ (by rw [tf, RingHom.map_one]) fun τ => by
        rw [ti, RingHom.map_one, RingHom.map_one]; rfl
      map_mul' := fun x y => ext _ _ (by rw [RingHom.map_mul, tf, tf, tf, mul_one]) fun τ => by
        rw [RingHom.map_mul, RingHom.map_mul, ti, ti, ti]; rfl }
  have Tc : Continuous T.toHomUnits := Units.continuous_iff.2 ⟨tc, tc.comp continuous_inv⟩
  have hT : ∀ x : (AE D)ˣ, c x = c (T.toHomUnits fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x) := by
    intro x
    have h1 : a x = T.toHomUnits fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x :=
      Units.ext (ext _ _ ((ha x).2.trans (tf _).symm) fun τ =>
        (congrArg (θ τ) (ha x).1).trans (ti (fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x) τ).symm)
    rw [← h1]
    conv_lhs => rw [hab x, map_mul, hf _ (hb x).1, mul_one]
  have hd : DenseRange fun (k : D.host.E) τ => tauE D τ k := by
    intro z
    have := mem_closure_range (tauE D) θ (fun τ => (hθ τ).1) (fun τ => (hθ τ).2) (infPart D (s z))
    rwa [show (fun i => θ i (infPart D (s z))) = z from funext fun τ => hs.comp z τ] at this
  intro x
  rw [hT]
  generalize (fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x) = z
  refine (denseRange_units (tauE D) hd).induction_on z
    (isClosed_eq (hc.1.comp Tc) continuous_const) fun k => ?_
  refine Eq.trans ?_ ((hT _).symm.trans (hc.2 k))
  congr 2
  funext τ
  exact Units.ext ((hθ τ).1 k).symm

end GlobalTheory.HeckeFinTrivial
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_normOne_root_congruent_odd_hostField : ∀ (D : D7) (N : ℕ), Odd N → ∀ u z : (Af D.host.F ⊗[D.host.F] D.host.E), z ∈ intAE D → u - 1 = N • z → u * sigR (Af D.host.F) D.sp.cm.sig u = 1 → ∃ x y : (Af D.host.F ⊗[D.host.F] D.host.E), x ∈ intAE D ∧ y ∈ intAE D ∧ x * y = 1 ∧ x = u * sigR (Af D.host.F) D.sp.cm.sig x ∧ ∃ p ∈ intAE D, x - 1 = N • p := by
  first | exact @GlobalTheory.OddRoot.exists_root_odd | exact GlobalTheory.OddRoot.exists_root_odd | (intros; apply GlobalTheory.OddRoot.exists_root_odd <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory

theorem genusMassStd_all : ∀ D : D7, GenusMassStd D :=
  genusMassStd_of_landherrHasse DefiniteOrthonormal.landherrHasse

end GlobalTheory
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.theta_span_rational_translates_vacuum : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), e0 ≠ 0 → ∀ F ∈ TT D (tor0 D cc δ) N N', ∃ (k : ℕ) (r : Fin k → ℂ) (z : Fin k → Matrix (Fin N') (Fin N) D.host.E), F = ∑ i, r i • Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) e0 := by
  first | exact @GlobalTheory.ThetaSpan.theta_span | exact GlobalTheory.ThetaSpan.theta_span | (intros; apply GlobalTheory.ThetaSpan.theta_span <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ArchFree.firstBasisVectorLike

open GlobalTheory.VacuumMove

theorem isVacuum_thetaIntertwiner_selfDual : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (a d : ℕ) L L' L₁ L₁', SD D L → SD D L' → SD D L₁ → SD D L₁' → ∀ G, ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G → ThetaVectorUpToUnits D (tor0 D cc δ) t0 L₁ L₁' (Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L L') (La D (tor0 D cc δ) L₁ L₁') (G : VC D a d → ℂ)) := by
  rintro D cc δ t0 hc ht a d L L' L₁ L₁' hL hL' hL₁ hL₁' G ⟨b, κ, hb, hκ, rfl⟩
  obtain ⟨μ, hμ, h⟩ := GlobalTheory.T.admissible_characters_exist D cc δ hc a d _ _ _ (Or.inl ⟨_, b, hb, rfl⟩) (Or.inr ⟨L, L', hL, hL', rfl⟩)
    (Or.inr ⟨L₁, L₁', hL₁, hL₁', rfl⟩) _ (pullbackOrthonormal_normalizedTheta_mem_thetaSpace D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ t0 hc ht b hb.1)
  refine ⟨b, κ * μ, hb, mod1All_mul hκ hμ, funext fun z => ?_⟩
  rw [Iop_mul, mul_assoc κ μ]
  exact congrArg (κ * ·) (congrFun h z)

end GlobalTheory.ArchFree.firstBasisVectorLike
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.cmQuadraticPhase_equivariant_embeddings : ∀ D : D7, galPh1 D := by
  first | exact @GlobalTheory.QuadPhase.galPh1_all | exact GlobalTheory.QuadPhase.galPh1_all | (intros; apply GlobalTheory.QuadPhase.galPh1_all <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.thetaPullbackConstant_sq_eq_det : ∀ D : D7, LemmaCGaussConstant D := by
  first | exact @GlobalTheory.UnitaryTheta.const_sq_eq_det | exact GlobalTheory.UnitaryTheta.const_sq_eq_det | (intros; apply GlobalTheory.UnitaryTheta.const_sq_eq_det <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.unitaryThetaConstant_eq_inverseDeterminantPhase : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (A A₁ : AddSubgroup (VC D N N')), KLat D (tor0 D cc δ) A → KLat D (tor0 D cc δ) A₁ → ∀ (u : VC D N N' ≃ₗ[ℂ] VC D N N'), (∀ z w, Hf D (tor0 D cc δ) (u z) (u w) = Hf D (tor0 D cc δ) z w) → (∀ x, x ∈ A ↔ u x ∈ A₁) → LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')) ≠ 0 → (∃ m : ℕ, 0 < m ∧ ∀ x ∈ A, ∃ y ∈ A, u.symm y ∈ A ∧ m • x = y - u.symm y) → ∀ (P S : VC D N N' →ₗ[ℂ] VC D N N'), (∀ x ∈ A, P x ∈ A ∧ S x ∈ A) → (∀ x, P (P x) = P x) → (∀ x y, Hf D (tor0 D cc δ) (P x) y = Hf D (tor0 D cc δ) x (P y)) → (∀ x, S (S x) = x) → (∀ x y, Hf D (tor0 D cc δ) (S x) (S y) = Hf D (tor0 D cc δ) x y) → (∀ x, S (P x) = S x - P (S x)) → (∀ x, P (u x) = u (P x)) → (∀ x, S (u x) = u (S x)) → (∀ M : ℕ, 0 < M → ∃ L B : VC D N N' →ₗ[ℂ] VC D N N', (∀ x ∈ A, L x ∈ A ∧ B x ∈ A) ∧ (∀ x, L (u x) = u (L x)) ∧ (∀ x, B (u x) = u (B x)) ∧ (∀ x, L (P x) = P (L x)) ∧ (∀ x y, Hf D (tor0 D cc δ) (B x) y = Hf D (tor0 D cc δ) x (B y)) ∧ ∀ x y, Hf D (tor0 D cc δ) (L x) (L y) = -Hf D (tor0 D cc δ) x y + M * Hf D (tor0 D cc δ) (B x) y) → ∀ th ∈ ThSp D (tor0 D cc δ) A, (fun z => th (u.symm z)) = ((‖LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N'))‖ : ℂ) / LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N'))) • Iop D (tor0 D cc δ) A A₁ th := by
  first | exact @GlobalTheory.SymConst.const_of_symm | exact GlobalTheory.SymConst.const_of_symm | (intros; apply GlobalTheory.SymConst.const_of_symm <;> assumption)
end
