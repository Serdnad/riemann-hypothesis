module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1396
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1293
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle005
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.UnitaryConjIff
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SubSplit
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2101
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def colv (m : ℕ) (bs : Module.Basis (Fin 2) F E) : (Fin m × Fin 2 → AF F) ≃ₜ+ (Fin m → AE F E) :=
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  { toFun v a := cmbE bs fun t => v (a, t)
    invFun z p := (Algebra.TensorProduct.basis (AF F) bs).repr (z p.1) p.2
    left_inv v := by
      funext p
      exact repr_cmbE_apply bs _ p.2
    right_inv z := by
      funext a
      exact cmbE_repr bs (z a)
    map_add' v w := by
      funext a
      simp only [cmbE, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    continuous_toFun := by
      refine continuous_pi fun a => ?_
      have h : (fun v : Fin m × Fin 2 → AF F => cmbE bs fun t => v (a, t)) =
          (GlobalTheory.JacSubst.coordCE F E bs).symm ∘ fun v t => v (a, t) := by
        funext v
        simp only [Function.comp_apply, cmbE_eq]
        change _ = (Algebra.TensorProduct.basis (AF F) bs).equivFun.symm (fun t => v (a, t))
        rw [Module.Basis.equivFun_symm_apply]
      rw [h]
      exact (GlobalTheory.JacSubst.coordCE F E bs).symm.continuous.comp (continuous_pi fun t => continuous_apply _)
    continuous_invFun := by
      refine continuous_pi fun p => ?_
      exact (continuous_apply p.2).comp ((GlobalTheory.JacSubst.coordCE F E bs).continuous.comp (continuous_apply p.1)) }

theorem Lc_eq_colv {m : ℕ} (bs : Module.Basis (Fin 2) F E) (M : Matrix (Fin m) (Fin m) (AE F E))
    (v : Fin m × Fin 2 → AF F) : Lc bs M v = (colv m bs).symm (M *ᵥ colv m bs v) := rfl

def HaarLc : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (m : ℕ) (J : Matrix (Fin m) (Fin m) E), J.det ≠ 0 → ∀ (bs : Module.Basis (Fin 2) F E) (g : UA σ J)
    (μ : @Measure (Fin m × Fin 2 → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ f : (Fin m × Fin 2 → AF F) → ℝ≥0∞, ∫⁻ x, f (Lc bs (mat g) x) ∂μ = ∫⁻ x, f x ∂μ

end PositivityTheory.SiegelWeilFormula.Ald

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

open PositivityTheory.SiegelWeilFormula.Ald.YFA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}


omit [NumberField F] in
theorem frame_of {n : ℕ} (hc : ∀ z : E, σ (σ z) = z) {J : Matrix (Fin n) (Fin n) E} {e₀ : E} (he : e₀ * e₀ = 1)
    (hJ : ∀ i j, σ (J j i) = e₀ * J i j) (T : GL (Fin n) E) (hT : J * T.1.map σ = 1) :
    ∃ b : GL (Fin n ⊕ Fin n) E, b.1ᵀ * dbl J * b.1.map σ = Matrix.fromBlocks 0 1 (e₀ • 1) 0 ∧
      ∃ t : GL (Fin n) E, b.1.toCols₁ = diagCols (Fin n) * t.1 := by
  have h2 : (2 : E) ≠ 0 := two_ne_zero
  have ha : (2 : E)⁻¹ + (σ : E →+* E) (2 : E)⁻¹ = 1 := by
    rw [map_inv₀, map_ofNat, ← two_mul, mul_inv_cancel₀ h2]
  have hJ' : (J.map (σ : E →+* E))ᵀ = e₀ • J := by
    ext i j
    simpa using hJ i j
  have hT' : (1 : GL (Fin n) E).1ᵀ * J * (1 : GL (Fin n) E).1.map (σ : E →+* E) * T.1.map (σ : E →+* E) = 1 := by
    have : (1 : Matrix (Fin n) (Fin n) E).map (σ : E →+* E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
    simpa [this] using hT
  refine ⟨GlobalTheory.ThK.Dbl.Frame.two 1 * GlobalTheory.ThK.Dbl.Frame.wit (2 : E)⁻¹ T,
    GlobalTheory.ThK.Dbl.Frame.frame_gram (σ : E →+* E) hc he ha hJ' 1 T hT', toCols₁_wit T _⟩

theorem yFrame : YFrame := by
  intro F E _ _ _ _ _ σ d n hN hn
  have hc : ∀ z : E, σ (σ z) = z := sig_sig' d.ok.good.cm
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  have hεσ : σ (((ε : ℤ) : E)) = ((ε : ℤ) : E) := map_intCast σ _
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
  · obtain ⟨ξ, hξ, hσξ⟩ := GlobalTheory.T.exists_ne_zero_conj_neg_of_cmExtension F E σ d.B d.ok.good
    have hξ' : -ξ ≠ 0 := neg_ne_zero.2 hξ
    let J : Matrix (Fin n) (Fin n) E := ξ • 1
    have hJ : ∀ i j, σ (J j i) = (-1) * J i j := fun i j => by
      by_cases h : i = j
      · subst h; simp [J, hσξ]
      · simp [J, Matrix.one_apply, h, Ne.symm h]
    let T : GL (Fin n) E := ⟨(-ξ)⁻¹ • 1, (-ξ) • 1,
      by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, inv_mul_cancel₀ hξ', one_smul],
      by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hξ', one_smul]⟩
    have hm : T.1.map σ = ξ⁻¹ • 1 := by
      ext i j
      by_cases h : i = j
      · subst h; simp [T, map_inv₀, hσξ]
      · simp [T, Matrix.one_apply, h]
    have hT : J * T.1.map σ = 1 := by
      rw [hm, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hξ, one_smul]
    obtain ⟨b, hb, hd⟩ := frame_of hc (by norm_num) hJ T hT
    have hεv : ((ε : ℤ) : E) = -1 :=
      eps_eq (by omega) hc (fun i j => by rw [hY]; ring) hε hεσ
    refine ⟨spcOf F J, b, ε, Or.inl ⟨hA, fun i j => (by simpa using hJ i j : σ (J j i) = -J i j)⟩, ⟨⟨ε, ?_⟩, hd⟩, hε, ?_⟩ <;>
      · change b.1ᵀ * dbl J * b.1.map σ = _
        try simp only [jeps]
        rw [hεv]; exact hb
  · let J : Matrix (Fin n) (Fin n) E := 1
    have hJ : ∀ i j, σ (J j i) = 1 * J i j := fun i j => by
      by_cases h : i = j
      · subst h; simp [J]
      · simp [J, Matrix.one_apply, h, Ne.symm h]
    have hT : J * (1 : GL (Fin n) E).1.map σ = 1 := by
      simp [J, Matrix.map_one _ (map_zero σ) (map_one σ)]
    obtain ⟨b, hb, hd⟩ := frame_of hc (by norm_num) hJ 1 hT
    have hεv : ((ε : ℤ) : E) = 1 :=
      eps_eq (by omega) hc (fun i j => by rw [hY]; ring) hε hεσ
    refine ⟨spcOf F J, b, ε, Or.inr ⟨hA, fun i j => (by simpa using hJ i j : σ (J j i) = J i j)⟩, ⟨⟨ε, ?_⟩, hd⟩, hε, ?_⟩ <;>
      · change b.1ᵀ * dbl J * b.1.map σ = _
        try simp only [jeps]
        rw [hεv]; exact hb

end PositivityTheory.SiegelWeilFormula.Ald

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

set_option linter.unusedSectionVars false

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem embQ_mul_left {m n N : ℕ} (h : n + 1 = N) (L : Matrix (Fin m) (Fin m) (AE F E))
    (Q : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) : L * embQ h Q = embQ h (L * Q) := by
  ext a c
  simp only [embQ, Matrix.mul_apply, Matrix.submatrix_apply, id]
  rcases eB h c with x | x <;> simp [Matrix.mul_apply]

theorem embQ_map_apply {R : Type*} [Zero R] {m n N : ℕ} (h : n + 1 = N) (Q : Matrix (Fin m) (Fin n ⊕ Fin n) R)
    (a : Fin m) (v : Fin n ⊕ Fin n) : embQ h Q a (Sum.map (em0 h) (em0 h) v) = Q a v := by
  simp [embQ, eB_map]

theorem frQ_left {m k : ℕ} (c : GL (Fin k ⊕ Fin k) E) (L : Matrix (Fin m) (Fin m) (AE F E))
    (w : Matrix (Fin m) (Fin k ⊕ Fin k) (AE F E)) : frQ c (L * w) = L * frQ c w := by
  rw [frQ, frQ, Matrix.mul_assoc]

theorem chartFacts : ChartFacts := by
  intro F E _ _ _ _ _ σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' h0 h'
  have rdE : ∀ w, (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).e w = ((dd0.e w).1 ∘ eK d.m h, (dd0.e w).2 ∘ eK d.m h) :=
    fun w => by rw [GlobalTheory.TowU.reindexD_e, Equiv.symm_symm]
  have hfr : ∀ g, inFrame d.b (j g) = blk h (inFrame b g) 1 := fun g => eq_blk h _ _ (hj.2.1 g) (hj.2.2 g)
  refine ⟨fun w' => ?_, fun u v => ⟨_, LinearEquiv.apply_symm_apply _ _⟩, fun g w H1 H2 => ?_, fun g w' => ?_,
    fun u w' => ?_⟩
  ·
    rw [rdE, adapted_e h0, frQ_emb, embQ_toCols₁, embQ_toCols₂, adapted_e h']
    refine Prod.ext (funext fun q => ?_) (funext fun q => ?_)
    · rcases q with ⟨a, c, t⟩ | ⟨a, t⟩
      · exact crdB_col _ _ _ a _ c t (extend_zero_embedded_column h _ a c)
      · exact crdB_zero_col _ _ a _ t (extend_zero_last_column h _ a)
    · rcases q with ⟨a, c, t⟩ | ⟨a, t⟩
      · exact Bf_col _ _ _ _ a _ c t (fun p => extend_zero_embedded_column h _ p c)
      · exact Bf_zero_col _ _ _ a _ t (fun p => extend_zero_last_column h _ p)
  ·
    set Q := frQ d.b w with hQdef
    set Q' := Q.submatrix id (Sum.map (em0 h) (em0 h)) with hQ'def
    have hw := adapted_e h0 w
    have hz : dd0.e (embQ h Q' * (incM F d.b.1)ᵀ) = 0 := by
      rw [adapted_e h0, frQ_of, embQ_toCols₁, embQ_toCols₂]
      refine Prod.ext (funext fun q => ?_) (funext fun q => ?_)
      · obtain ⟨a, c, t⟩ := q
        by_cases hc : c = i0 h
        · subst hc
          exact crdB_zero_col _ _ a _ t (extend_zero_last_column h _ a)
        · obtain ⟨c', rfl⟩ := (ne_last_iff_mem_range h c).1 hc
          have e3 := congrFun H1 (a, c', t)
          rw [rdE, hw] at e3
          refine (crdB_col _ _ _ a _ _ t ?_).trans e3
          rw [extend_zero_embedded_column]
          rfl
      · obtain ⟨a, c, t⟩ := q
        by_cases hc : c = i0 h
        · subst hc
          exact Bf_zero_col _ _ _ a _ t (fun p => extend_zero_last_column h _ p)
        · obtain ⟨c', rfl⟩ := (ne_last_iff_mem_range h c).1 hc
          have e3 := congrFun H2 (a, c', t)
          rw [rdE, hw] at e3
          refine (Bf_col _ _ _ _ a _ _ t fun p => ?_).trans e3
          rw [extend_zero_embedded_column]
          rfl
    have hQ' : embQ h Q' = 0 := by
      have := (LinearEquiv.map_eq_zero_iff dd0.e).1 hz
      rw [← frQ_of d.b (embQ h Q'), this, frQ, Matrix.zero_mul]
    have hQv : ∀ a v', Q a (Sum.map (em0 h) (em0 h) v') = 0 := fun a v' => by
      have := congrFun (congrFun hQ' a) (Sum.map (em0 h) (em0 h) v')
      rwa [embQ_map_apply] at this
    apply frQ_injective d.b
    show frQ d.b (w * ((j g).1.1)ᵀ) = frQ d.b w
    rw [frQ_mul_mat, hfr, ← hQdef]
    ext a u
    rw [Matrix.mul_apply]
    have hterm : ∀ v, Q a v * (blk h (inFrame b g) 1)ᵀ v u = Q a v * (1 : Matrix (Fin d.n ⊕ Fin d.n) _ (AE F E)) u v := by
      intro v
      rcases idx_cases h v with ⟨v', rfl⟩ | hv | hv
      · rw [hQv, zero_mul, zero_mul]
      · rw [Matrix.transpose_apply, (blk_out h _ v (by rw [hv]; exact Or.inl rfl) u).2]
      · rw [Matrix.transpose_apply, (blk_out h _ v (by rw [hv]; exact Or.inr rfl) u).2]
    rw [Finset.sum_congr rfl fun v _ => hterm v]
    simp [Matrix.one_apply]
  ·
    apply frQ_injective d.b
    show frQ d.b (emb h b d.b w' * ((j g).1.1)ᵀ) = frQ d.b (emb h b d.b (w' * (g.1.1)ᵀ))
    rw [frQ_mul_mat, frQ_emb, frQ_emb, frQ_mul_mat, hfr, embQ_mul_blk]
  ·
    rw [emb_eq, emb_eq, frQ_left, ← embQ_mul_left, Matrix.mul_assoc]

end PositivityTheory.SiegelWeilFormula.Ald

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F : Type} [Field F] [NumberField F]

theorem schr_char {κ' κ'' : Type} [Fintype κ'] [Fintype κ''] (ψ : AddChar (AF F) ℂ) (v : κ'' → AF F)
    (Ψ : (κ' ⊕ κ'' → AF F) → ℂ) :
    schr ψ ((0 : κ' ⊕ κ'' → AF F), Sum.elim (0 : κ' → AF F) v) Ψ = fun z => ψ ((z ∘ Sum.inr) ⬝ᵥ v) * Ψ z := by
  funext z
  have hz : z = Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr) := (Sum.elim_comp_inl_inr z).symm
  simp only [schr, zero_dotProduct, mul_zero, add_zero]
  congr 2
  conv_lhs => rw [hz]
  rw [sumElim_dotProduct_sumElim]
  simp

theorem schr_transl {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (u : κ → AF F) (φ : (κ → AF F) → ℂ) (z : κ → AF F) :
    schr ψ (u, 0) φ z = φ (z + u) := by
  simp [schr]

theorem box_transl {κ' κ'' : Type} [Fintype κ'] [Fintype κ''] (ψ : AddChar (AF F) ℂ) (u : κ'' → AF F)
    (φ' : (κ' → AF F) → ℂ) (φ'' : (κ'' → AF F) → ℂ) :
    boxFun φ' (schr ψ (u, 0) φ'') = schr ψ (Sum.elim (0 : κ' → AF F) u, 0) (boxFun φ' φ'') := by
  funext x
  rw [schr_transl]
  simp only [boxFun]
  rw [schr_transl]
  congr 2
  funext i
  simp

theorem opBox_of (hP : PartCharInv) (hS : SliceFacts) : OpBox := by
  intro F _ _ ψ hψ κ' κ'' _ _ W _ _ B dd G _ act om hsp hw x hfix φ₀ hφ₀ h0
  have hcomm : ∀ w : W, (dd.e w).1 ∘ Sum.inl = 0 → (dd.e w).2 ∘ Sum.inl = 0 →
      ∀ Φ ∈ schA F (κ' ⊕ κ''), om x (schr ψ (dd.e w) Φ) = schr ψ (dd.e w) (om x Φ) := by
    intro w h1 h2 Φ hΦ
    have := hsp.impl x w Φ hΦ
    simpa only [Darboux.rho, hfix w h1 h2] using this
  have hvan : ∀ Δ ∈ schA F (κ' ⊕ κ''), (∀ a : κ' → AF F, Δ (a ⊕ᵥ 0) = 0) →
      ∀ a : κ' → AF F, om x Δ (a ⊕ᵥ 0) = 0 := by
    intro Δ hΔ hz a
    have hl := hsp.adm x _ ((GlobalTheory.T.adelicSchwartz_pointValues_admitted F ψ hψ (κ' ⊕ κ'')).1 (a ⊕ᵥ 0))
    have key := hP F ψ hψ κ' κ'' _ hl ?_ Δ hΔ hz
    · simpa using key
    · intro y Ψ hΨ
      obtain ⟨w, hw'⟩ := hw 0 y
      have e0 : ((0 : κ' → AF F) ⊕ᵥ (0 : κ'' → AF F)) = 0 := Sum.elim_zero_zero
      have hw0 : dd.e w = ((0 : κ' ⊕ κ'' → AF F), Sum.elim (0 : κ' → AF F) y) := by
        rw [hw', e0]
      have hrho : (fun z : κ' ⊕ κ'' → AF F => ψ ((z ∘ Sum.inr) ⬝ᵥ y) * Ψ z) = schr ψ (dd.e w) Ψ := by
        rw [hw0, schr_char]
      have h1 : (dd.e w).1 ∘ Sum.inl = 0 := by rw [hw0]; rfl
      have h2 : (dd.e w).2 ∘ Sum.inl = 0 := by rw [hw0]; rfl
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.proj_apply]
      rw [hrho, hcomm w h1 h2 Ψ hΨ, hw0, schr_char]
      simp
  refine ⟨?_, ?_⟩
  · intro Ψ hΨ
    have hs : slice0 κ' κ'' Ψ ∈ schA F κ' := (hS F κ' κ'').1 Ψ hΨ
    have hB := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ' κ'' _ hs φ₀ hφ₀
    have hD := hvan (Ψ - boxFun (slice0 κ' κ'' Ψ) φ₀) (Submodule.sub_mem _ hΨ hB) (by
      intro a
      simp [slice0, boxFun, h0])
    funext a
    have := hD a
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at this
    simpa [slice0] using this
  · intro φ' hφ' φ'' hφ''
    funext z
    obtain ⟨w, hw'⟩ := hw (z ∘ Sum.inr) 0
    have e0 : ((0 : κ' → AF F) ⊕ᵥ (0 : κ'' → AF F)) = 0 := Sum.elim_zero_zero
    have hw0 : dd.e w = (Sum.elim (0 : κ' → AF F) (z ∘ Sum.inr), (0 : κ' ⊕ κ'' → AF F)) := by
      rw [hw', e0]
    have h1 : (dd.e w).1 ∘ Sum.inl = 0 := by rw [hw0]; rfl
    have h2 : (dd.e w).2 ∘ Sum.inl = 0 := by rw [hw0]; rfl
    have hzs : z = (z ∘ Sum.inl ⊕ᵥ 0) + Sum.elim (0 : κ' → AF F) (z ∘ Sum.inr) := by
      funext i
      cases i <;> simp
    have hbox := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ' κ'' _ hφ' φ'' hφ''
    set η := schr ψ (z ∘ Sum.inr, 0) φ'' with hη
    have hηm : η ∈ schA F κ'' := (GlobalTheory.T.adelicSchwartz_pointValues_admitted F ψ hψ κ'').2.2.1 _ φ'' hφ''
    have hη0 : η 0 = φ'' (z ∘ Sum.inr) := by
      rw [hη, schr_transl, zero_add]
    have hL : om x (boxFun φ' φ'') z = om x (boxFun φ' η) (z ∘ Sum.inl ⊕ᵥ 0) := by
      rw [hη, box_transl, ← hw0, hcomm w h1 h2 _ hbox, hw0, schr_transl, ← hzs]
    have hB1 := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ' κ'' _ hφ' η hηm
    have hB2 := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ' κ'' _ hφ' φ₀ hφ₀
    have hD := hvan (boxFun φ' η - η 0 • boxFun φ' φ₀)
      (Submodule.sub_mem _ hB1 (Submodule.smul_mem _ _ hB2)) (by
        intro a
        simp [boxFun, h0]
        ring)
      (z ∘ Sum.inl)
    rw [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, sub_eq_zero, smul_eq_mul] at hD
    rw [hL, hD, hη0]
    simp [boxFun, slice0, mul_comm]

end PositivityTheory.SiegelWeilFormula.Ald

end
end
