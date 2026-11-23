module

public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle046
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle005
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle045
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle006
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogLeOfLePowMulPow
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle001
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem span_image_smul_top {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (c : K) (hc : c ≠ 0)
    (S : Set V) (hS : Submodule.span K S = ⊤) : Submodule.span K ((fun g => c • g) '' S) = ⊤ := by
  refine eq_top_iff.mpr fun v _ => ?_
  have key : ∀ x ∈ Submodule.span K S, c • x ∈ Submodule.span K ((fun g => c • g) '' S) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
    | smul e x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ e hx
  have hv : c⁻¹ • v ∈ Submodule.span K S := hS ▸ Submodule.mem_top
  simpa [smul_smul, hc] using key _ hv

theorem shortG_scaled : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (w : WeightFamilies.Wt D j) (s : 𝓞 B.KO) (Sh : Finset (B.Cusp j w)) (a b : ℝ), s ≠ 0 → 0 ≤ a → 0 ≤ b → (∀ σ : B.KO →+* ℂ, Real.log ‖σ (s : B.KO)‖ ≤ a) → (∀ g ∈ Sh, g ∈ X.shortTh w ∧ ∀ σ, Real.log (B.supN j w σ g) ≤ b) → Submodule.span B.KO (Sh : Set (B.Cusp j w)) = ⊤ → ShortG X w (X.Thc s w) (a + b + lamStar D * w.size) := by
  intro D B P j X w s Sh a b hs ha hb hsa hSh hspan
  classical

  let N : ℕ := D.host.g 0 * D.host.g 1
  let k : ℕ := D.R.f * D.R.r * w.n
  let t : 𝓞 B.KO := s * (N : 𝓞 B.KO) ^ k
  have hN1 : (1 : ℝ) ≤ N := by
    have h0 := (D.host.g_prime 0).one_lt
    have h1 := (D.host.g_prime 1).one_lt
    have : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    exact_mod_cast this
  have htK : ((t : 𝓞 B.KO) : B.KO) = (s : B.KO) * ((N : ℕ) : B.KO) ^ k := by
    simp [t]
  have hsK : (s : B.KO) ≠ 0 := fun h => hs (by exact_mod_cast h)
  have hNK : ((N : ℕ) : B.KO) ≠ 0 := by
    have : N ≠ 0 := by
      intro h; rw [h] at hN1; norm_num at hN1
    exact_mod_cast this
  have ht0 : ((t : 𝓞 B.KO) : B.KO) ≠ 0 := by
    rw [htK]; exact mul_ne_zero hsK (pow_ne_zero _ hNK)
  have hsm : ∀ g : B.Cusp j w, t • g = ((t : 𝓞 B.KO) : B.KO) • g := fun g =>
    (algebraMap_smul B.KO t g).symm
  have hlam : 0 ≤ Real.log N ∧ Real.log N ≤ lamStar D := by
    have h2 := (pPow_size D j w).2.2.1
    refine ⟨Real.log_nonneg hN1, ?_⟩
    unfold Formalism.MainNotions.WeightAlgebra.lamStar
    have : ((N : ℕ) : ℝ) = (D.host.g 0 : ℝ) * D.host.g 1 := by simp [N]
    rw [← this]; linarith
  have hk : (k : ℝ) ≤ w.size := by
    unfold WeightFamilies.Wt.size
    have hm : (1 : ℝ) ≤ ((max (D.R.sigW j).2 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
    have hsum : 0 ≤ ∑ τ, ((∑ i, (w.aP τ i : ℝ)) + ∑ i, (w.aM τ i : ℝ)) := by positivity
    have : (k : ℝ) ≤ (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) := by
      calc (k : ℝ) = (D.R.f : ℝ) * 1 * (D.R.r : ℝ) * (w.n : ℝ) := by simp [k]
        _ ≤ _ := by gcongr
    linarith
  refine ⟨Sh.image fun g => t • g, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    simp only [PJ.Thc, PJ.scaled]
    refine Submodule.mem_map.mpr ⟨((N : 𝓞 B.KO) ^ k) • g, Submodule.mem_map.mpr ⟨g, (hSh g hg).1, by simp [N, k]⟩, ?_⟩
    simp only [t, mul_smul, LinearMap.smul_apply, LinearMap.id_apply]
  · have : ((Sh.image fun g => t • g : Finset (B.Cusp j w)) : Set (B.Cusp j w)) =
        (fun g => ((t : 𝓞 B.KO) : B.KO) • g) '' (Sh : Set (B.Cusp j w)) := by
      rw [Finset.coe_image]
      exact congrArg (· '' (Sh : Set (B.Cusp j w))) (funext hsm)
    rw [this]
    exact span_image_smul_top _ ht0 _ hspan
  · intro x hx
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hx
    apply WeightFamilies.meanLogSup_le
    intro σ
    rw [hsm, B.supN_smul, htK]
    have hσs : 0 < ‖σ (s : B.KO)‖ := norm_pos_iff.mpr ((map_ne_zero σ).mpr hsK)
    have hnorm : ‖σ ((s : B.KO) * ((N : ℕ) : B.KO) ^ k)‖ = ‖σ (s : B.KO)‖ * (N : ℝ) ^ k := by
      simp
    rw [hnorm]
    have hlog_s := hsa σ
    have hG := (hSh g hg).2 σ
    have hkN : (k : ℝ) * Real.log N ≤ lamStar D * w.size := by
      calc (k : ℝ) * Real.log N ≤ w.size * Real.log N := mul_le_mul_of_nonneg_right hk hlam.1
        _ ≤ w.size * lamStar D :=
            mul_le_mul_of_nonneg_left hlam.2 (by linarith [WeightFamilies.Wt.one_le_size w])
        _ = lamStar D * w.size := mul_comm _ _
    by_cases hg0 : B.supN j w σ g = 0
    · rw [hg0, mul_zero, Real.log_zero]
      have : 0 ≤ lamStar D * w.size :=
        mul_nonneg (hlam.1.trans hlam.2) (by linarith [WeightFamilies.Wt.one_le_size w])
      linarith
    · have hNk : (0 : ℝ) < (N : ℝ) ^ k := pow_pos (by linarith) _
      rw [Real.log_mul (mul_pos hσs hNk).ne' hg0, Real.log_mul hσs.ne' hNk.ne', Real.log_pow]
      linarith

end GlobalTheory.RunIn
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

theorem _root_.GlobalTheory.T.supBounds_le_generatorConstant_mul_size : ∀ (D : D7) (B : WeightFamilies.Prov D) (large₂ : SizeData₂ D) (j : ℕ) (w : WeightFamilies.Wt D j) (p : ℕ), 2 ≤ large₂.sc.L → 0 < w.n → (140 * D.R.r * large₂.sc.L * absA w + 10 * large₂.sc.L * absA w + 200 * D.R.f * D.R.r * w.n * large₂.sc.L ≤ 400 * Zb D large₂ * w.size) ∧ (2 * (lamStar D + 2 * Real.log p) * w.size + 400 * Zb D large₂ * w.size + lamStar D * w.size ≤ WeightAlgebra.Gc large₂ B (1009 * Zb D large₂) p * w.size) ∧ ((lamStar D + 2 * Real.log p) * w.size + (400 * Zb D large₂ * w.size + 3 * D.R.f * D.R.r * w.n * large₂.sc.L + 5 * Real.log (Module.finrank ℚ B.KO) + Real.log |((NumberField.discr B.KO : ℤ) : ℝ)| / Module.finrank ℚ B.KO + 2) ≤ WeightAlgebra.Gc large₂ B (1009 * Zb D large₂) p * w.size) := by
  first | exact @GlobalTheory.RunIn.sup_bounds_le_Gc | exact GlobalTheory.RunIn.sup_bounds_le_Gc | (intros; apply GlobalTheory.RunIn.sup_bounds_le_Gc <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory

section

variable {E : Type} [Field E] [NumberField E] {dim : (E →+* ℂ) → ℕ}

theorem levReps_act_mul (a b : 𝓞 E) (v : I2.Vsp dim) : I2.act a (I2.act b v) = I2.act (a * b) v := by
  ext i
  simp only [I2.act, RingOfIntegers.coe_eq_algebraMap, map_mul]
  exact (mul_assoc _ _ _).symm

theorem levReps_act_nat (m : ℕ) (v : I2.Vsp dim) : I2.act (m : 𝓞 E) v = (m : ℂ) • v := by
  ext i
  simp [I2.act]

theorem levReps_act_smul (a : 𝓞 E) (c : ℂ) (v : I2.Vsp dim) : I2.act a (c • v) = c • I2.act a v := by
  ext i
  simp [I2.act]
  ring

theorem levReps_act_add (a : 𝓞 E) (v w : I2.Vsp dim) : I2.act a (v + w) = I2.act a v + I2.act a w := by
  ext i
  simp [I2.act, mul_add]

theorem levReps_act_neg (a : 𝓞 E) (v : I2.Vsp dim) : I2.act a (-v) = -I2.act a v := by
  ext i
  simp [I2.act]

end

theorem isReps_level_translates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (T : I2.PT E) (mk : Dw.La →+ I2.Vsp T.dim) (α : 𝓞 E), α * H.bar α = (l.M : 𝓞 E) → l.Mb = Ideal.span {H.bar α} → (∀ a, mk a ∈ T.L) → (∀ (β : 𝓞 E) a, mk (β • a) = I2.act β (mk a)) → (∀ a, (∃ v ∈ T.L, mk a = (l.M : ℂ) • v) → ∃ b, a = l.M • b) → (∀ v ∈ T.L, ∃ a, ∃ v' ∈ T.L, v = mk a + (l.M : ℂ) • v') → ∀ x2 : LevQ Dw l → Dw.La, (∀ q, x2 q ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ q, x2 q - levRep q ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → ∀ n : ℕ, ∃ K : Finset (Fin n → I2.Vsp T.dim), I2.IsReps T l.M n (vspActL α) K ∧ ∀ b ∈ K, ∃ q : Fin n → LevQ Dw l, b = fun i => I2.act (H.bar α) (-(((l.M : ℂ) ^ 2)⁻¹ • mk (x2 (q i)))) := by
  intro E _ _ _ H Dw l T mk α hα hMb hL hlin hinj hsurj x2 hx2 hrep n
  classical
  haveI : Finite (LevQ Dw l) := (card_levQ E H Dw l).1
  haveI : Fintype (LevQ Dw l) := Fintype.ofFinite _
  have hM : (l.M : ℂ) ≠ 0 := by
    have := l.three_le
    exact Nat.cast_ne_zero.2 (by omega)
  have hbb : H.bar (H.bar α) = α := by
    apply Subtype.ext
    change ((H.bar (H.bar α) : 𝓞 E) : E) = (α : E)
    rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]
  have hmap : l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {α} := by
    rw [hMb, Ideal.map_span, Set.image_singleton]
    exact congrArg (fun z => Ideal.span {z}) hbb
  have hsm : ∀ (c : 𝓞 E) (y : Dw.La), y ∈ Ideal.span {c} • (⊤ : Submodule (𝓞 E) Dw.La) ↔ ∃ z, y = c • z := by
    intro c y
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨fun ⟨z, _, h⟩ => ⟨z, h.symm⟩, fun ⟨z, h⟩ => ⟨z, trivial, h.symm⟩⟩
  have hu : ∀ q, ∃ u : Dw.La, x2 q = α • α • u := by
    intro q
    have h := hx2 q
    rw [hmap, Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton, hsm] at h
    obtain ⟨z, hz⟩ := h
    refine ⟨(2 : 𝓞 E) • z, ?_⟩
    rw [hz, smul_smul, smul_smul]
    congr 1
    ring
  have hcls : ∀ q, (Submodule.Quotient.mk (x2 q) : LevQ Dw l) = q := by
    intro q
    rw [(Submodule.Quotient.eq _).2 (hrep q)]
    exact Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)
  obtain ⟨r, s, hrs⟩ : ∃ r s : 𝓞 E, r * H.bar α + s * α = 1 := by
    have h := l.coprime
    rw [hmap, hMb, Ideal.eq_top_iff_one, ← Ideal.span_insert, Ideal.mem_span_pair] at h
    exact h
  set t : LevQ Dw l → I2.Vsp T.dim := fun q => I2.act (H.bar α) (-(((l.M : ℂ) ^ 2)⁻¹ • mk (x2 q))) with ht
  have hαt : ∀ q, I2.act α (t q) = -((l.M : ℂ)⁻¹ • mk (x2 q)) := by
    intro q
    simp only [ht]
    rw [levReps_act_mul, hα, levReps_act_nat, smul_neg, smul_smul]
    congr 2
    field_simp
  have hMt : ∀ q, (l.M : ℂ) • t q ∈ T.L := by
    intro q
    obtain ⟨u, hq⟩ := hu q
    have : (l.M : ℂ) • t q = -mk (α • u) := by
      simp only [ht]
      rw [hq, hlin α (α • u), levReps_act_neg, levReps_act_smul, levReps_act_mul, mul_comm (H.bar α), hα,
        levReps_act_nat, smul_neg, smul_smul, smul_smul]
      have : (l.M : ℂ) * ((l.M : ℂ) ^ 2)⁻¹ * l.M = 1 := by field_simp
      rw [this, one_smul]
    rw [this]
    exact T.L.neg_mem (hL _)
  have hsub : ∀ (b : I2.Vsp T.dim) q, vspActL α (b - t q) = I2.act α b + (l.M : ℂ)⁻¹ • mk (x2 q) := by
    intro b q
    rw [map_sub]
    change I2.act α b - I2.act α (t q) = _
    rw [hαt, sub_neg_eq_add]
  have hex : ∀ b : I2.Vsp T.dim, (l.M : ℂ) • b ∈ T.L → ∃ q, vspActL α (b - t q) ∈ T.L := by
    intro b hb
    obtain ⟨a, v', hv', hab⟩ := hsurj _ hb
    refine ⟨Submodule.Quotient.mk (-(α • a)), ?_⟩
    set q : LevQ Dw l := Submodule.Quotient.mk (-(α • a)) with hq
    have h1 : x2 q - -(α • a) ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) :=
      (Submodule.Quotient.eq _).1 ((hcls q).trans hq)
    rw [hMb, hsm] at h1
    obtain ⟨d, hd⟩ := h1
    obtain ⟨u, hqu⟩ := hu q
    have h2 : x2 q + α • a = (l.M : 𝓞 E) • (r • (α • u + a) + s • d) := by
      have e1 : x2 q + α • a = α • (α • u + a) := by rw [hqu, smul_add]
      have e2 : x2 q + α • a = H.bar α • d := by rw [← hd, sub_neg_eq_add]
      calc x2 q + α • a = (r * H.bar α + s * α) • (x2 q + α • a) := by rw [hrs, one_smul]
        _ = (r * H.bar α) • α • (α • u + a) + (s * α) • H.bar α • d := by rw [add_smul, ← e1, ← e2]
        _ = _ := by
          rw [← hα, smul_add (α * H.bar α)]
          simp only [smul_smul (r * H.bar α), smul_smul (s * α), smul_smul (α * H.bar α)]
          congr 2 <;> ring
    have hb' : b = (l.M : ℂ)⁻¹ • mk a + v' := by
      calc b = (l.M : ℂ)⁻¹ • (l.M : ℂ) • b := by rw [smul_smul, inv_mul_cancel₀ hM, one_smul]
        _ = _ := by rw [hab, smul_add, smul_smul, inv_mul_cancel₀ hM, one_smul]
    have h3 : vspActL α (b - t q) = mk (r • (α • u + a) + s • d) + I2.act α v' := by
      rw [hsub, hb', levReps_act_add, levReps_act_smul, ← hlin, add_right_comm, ← smul_add, ← map_add (f := _),
        add_comm (α • a), h2, hlin, levReps_act_nat, smul_smul, inv_mul_cancel₀ hM, one_smul]
    rw [h3]
    exact T.L.add_mem (hL _) (T.stable _ _ hv')
  have huniq : ∀ (b : I2.Vsp T.dim) q q', vspActL α (b - t q) ∈ T.L → vspActL α (b - t q') ∈ T.L → q = q' := by
    intro b q q' h h'
    have h1 := T.L.sub_mem h h'
    rw [hsub, hsub, add_sub_add_left_eq_sub, ← smul_sub, ← map_sub] at h1
    obtain ⟨z, hz⟩ := hinj (x2 q - x2 q') ⟨_, h1, by rw [smul_smul, mul_inv_cancel₀ hM, one_smul]⟩
    rw [← hcls q, ← hcls q']
    refine (Submodule.Quotient.eq _).2 ?_
    rw [hMb, hsm]
    exact ⟨α • z, by rw [hz, smul_smul, mul_comm, hα, Nat.cast_smul_eq_nsmul]⟩
  refine ⟨Finset.univ.image (fun q : Fin n → LevQ Dw l => fun i => t (q i)), ⟨?_, ?_⟩, ?_⟩
  · intro b hb k
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hb
    exact hMt _
  · intro b hb
    choose q hq using fun k => hex (b k) (hb k)
    refine ⟨fun i => t (q i), ⟨Finset.mem_image.2 ⟨q, Finset.mem_univ _, rfl⟩, hq⟩, ?_⟩
    rintro b' ⟨hb', h'⟩
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hb'
    funext k
    rw [huniq (b k) _ _ (h' k) (hq k)]
  · intro b hb
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hb
    exact ⟨q, rfl⟩

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RunIn

theorem log_two_mul_count_le_mul_size : ∀ (D : D7) (B : WeightFamilies.Prov D) (large₂ : SizeData₂ D) (j : ℕ) (w : WeightFamilies.Wt D j) (N : ℕ) (Prw : ℝ), 2 ≤ large₂.sc.L → 0 < w.n → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → OPO large₂ B → 38 * large₂.sc.L + PO D large₂ ≤ Prw → N ≤ 2 * ((D.host.g 0 * D.host.g 1) ^ (D.R.f * D.R.r * w.n) * (Module.finrank ℚ B.KO * (1 + WeightAlgebra.DF w) ^ (D.R.f * D.R.r * w.n))) → Real.log N ≤ Prw * (w.size - 1) := by
  intro D B large₂ j w N Prw hL hn hrows hO hPrw hN
  obtain ⟨hg, -, -, -, -, -, -, hX, -⟩ := hrows

  set m : ℕ := D.R.f * D.R.r * w.n with hm
  have hN' : N ≤ (D.host.g 0 * D.host.g 1) ^ m * ((2 * Module.finrank ℚ B.KO) * (1 + WeightAlgebra.DF w) ^ m) := by
    calc N ≤ _ := hN
      _ = _ := by ring
  have hL0 : (0 : ℝ) ≤ large₂.sc.L := by linarith
  have hPO : 0 ≤ PO D large₂ := by unfold PO; positivity
  have hd : Real.log ((2 * Module.finrank ℚ B.KO : ℕ) : ℝ) ≤ PO D large₂ + 1 := by
    rcases Nat.eq_zero_or_pos (Module.finrank ℚ B.KO) with h0 | hpos
    · simp [h0]; linarith
    · have hk : ((Module.finrank ℚ B.KO : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
      push_cast
      rw [Real.log_mul (by norm_num) hk]
      have h2 : Real.log 2 ≤ 1 := by
        have := Real.log_two_lt_d9; linarith
      linarith [hO.1]
  have hX' : Real.log ((1 + WeightAlgebra.DF w : ℕ) : ℝ) ≤ 2 * large₂.sc.L := by
    push_cast; exact hX
  have key := log_le_of_le_pow_mul_pow (a := 9 * large₂.sc.L + 1) (c := 2 * large₂.sc.L) (P := PO D large₂ + 1)
    (by linarith) (by linarith) (by linarith) (hg 0) (hg 1) hd hX' hN'

  have hf : 0 < D.R.f := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_le_f
    have h3 : D.R.f = 2 * D.R.ord := rfl
    omega
  have hr : 0 < D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    have h3 : D.R.r = D.R.k + D.R.m - 1 := rfl
    omega
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    have : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (by positivity)
    exact_mod_cast this
  have hms : (m : ℝ) ≤ w.size - 1 := frn_le_size_sub_one w
  have hPrw0 : 0 ≤ Prw := by linarith
  calc Real.log N ≤ (m : ℝ) * (2 * (9 * large₂.sc.L + 1) + 2 * large₂.sc.L) + (PO D large₂ + 1) := key
    _ ≤ (m : ℝ) * (38 * large₂.sc.L + PO D large₂) := by nlinarith
    _ ≤ (m : ℝ) * Prw := by gcongr
    _ ≤ Prw * (w.size - 1) := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hms hPrw0

end GlobalTheory.RunIn
end
