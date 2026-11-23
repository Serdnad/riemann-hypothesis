module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle060
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle005
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle006
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.UnitaryConjIff
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle069
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle032
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle058
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.ProdGenMem
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.Bundle001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.SubMulRight
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle028
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle054
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle070
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitIwa
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ParabolicLowerBlockZero
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
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle002
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem chartFacts_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.ChartFacts_k := by
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
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
open Matrix
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem om_place_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hLO : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hLI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) :
    ∃ (p q : ℕ) (e : ℤ), ∀ y : GR d.n, InK (mR y) → ∀ g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d), ∀ Ω ∈ d.sch, d.T Ω = _root_.PositivityTheory.SiegelWeilFormula.KFP.vac_k R g →
      d.om (R.ι w y) Ω = F0 p q e y • Ω := by
  obtain ⟨L, hL⟩ := hLO F E σ d R w
  obtain ⟨sL, ρ, p, q, e, -, hLD, -, hLk⟩ := hLI F E σ d R w L hL
  refine ⟨p, q, e, fun y hy g hg Ω hΩ hTΩ => ?_⟩
  let Ψ : Mx F E d.m d.n → ℂ := fun X =>
    (∏ w' ∈ Finset.univ.erase w, fP (1 : PX d.m d.n) (R.loc w' X)) * g (fun k => (d.crd X k).2)
  have hΨ : Ψ ∈ R.away w := Submodule.subset_span ⟨fun _ => 1, g, hg, rfl⟩
  have hvt : d.T Ω = R.tens w (fP (1 : PX d.m d.n)) Ψ := by
    rw [hTΩ]
    funext X
    simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.vac_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.gau_k, _root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k, Ψ]
    rw [← Finset.mul_prod_erase Finset.univ (fun w' => fP (1 : PX d.m d.n) (R.loc w' X)) (Finset.mem_univ w), mul_assoc]
    rfl
  have h1 := (hL y (fP (1 : PX d.m d.n)) (KFock.isSw_fP 1)).2 Ψ (_root_.PositivityTheory.SiegelWeilFormula.KFock.away_inv_k R w Ψ hΨ) Ω hΩ hvt
  rw [hLk y 1 hy, hLD.kvac y hy] at h1
  have hfP : fP (F0 p q e y • (1 : PX d.m d.n)) = F0 p q e y • fP (1 : PX d.m d.n) := by
    funext u
    simp only [fP, evX, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, Pi.smul_apply, smul_eq_mul]
    ring
  have htens : R.tens w (F0 p q e y • fP (1 : PX d.m d.n)) Ψ = F0 p q e y • R.tens w (fP (1 : PX d.m d.n)) Ψ := by
    funext X
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfP, htens, ← hvt, ← _root_.PositivityTheory.SiegelWeilFormula.KFock.T_smul_k] at h1
  have hS := d.ok.dbl.weil.2.1.toIsSplitting
  exact _root_.PositivityTheory.SiegelWeilFormula.KFock.T_inj_k hT.1 d (hS.pres _ Ω hΩ) (d.sch.smul_mem _ hΩ) h1
theorem om_rot_vac'_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hLO : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hLI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (t : ℝ) :
    ∃ χ : ℂ, χ ≠ 0 ∧ ∀ g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d), ∀ Ω ∈ d.sch, d.T Ω = _root_.PositivityTheory.SiegelWeilFormula.KFP.vac_k R g → d.om (_root_.PositivityTheory.SiegelWeilFormula.KFP.rot_k R t) Ω = χ • Ω := by
  have key : ∀ l : List (InfinitePlace F), ∃ χ : ℂ, χ ≠ 0 ∧ ∀ g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d), ∀ Ω ∈ d.sch, d.T Ω = _root_.PositivityTheory.SiegelWeilFormula.KFP.vac_k R g →
      d.om ((l.map fun w => R.ι w (yrot d.n (R.sg w) t)).prod) Ω = χ • Ω := by
    intro l
    induction l with
    | nil => exact ⟨1, one_ne_zero, fun g _ Ω _ _ => by simp⟩
    | cons w l ih =>
      obtain ⟨χ, hχ, h⟩ := ih
      obtain ⟨p, q, e, hw⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFP.om_place_k hT hLO hLI R w
      refine ⟨F0 p q e (yrot d.n (R.sg w) t) * χ, mul_ne_zero (weight_factor_rotation_ne_zero p q e d.n (R.sg w) t) hχ,
        fun g hg Ω hΩ hTΩ => ?_⟩
      have hK : InK (mR (yrot d.n (R.sg w) t)) := by rw [mR_yrot]; exact inK_yrotM' _ _ _
      rw [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, h g hg Ω hΩ hTΩ, map_smul,
        hw _ hK g hg Ω hΩ hTΩ, smul_smul, mul_comm]
  exact key _
end PositivityTheory.SiegelWeilFormula.KFP
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Avac
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem frame_formE_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ)
    (h : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ) = Jm d.n ((ε : ℤ) : AE F E) := by
  have e1 : (incM F d.b.1).map (cA σ) = incM F (d.b.1.map σ) := by
    ext i j
    simp [incM, cA, inclR, Algebra.TensorProduct.map_tmul]
  have e2 : dbl (incM F d.Y.J) = incM F (dbl d.Y.J) := by
    simp [dbl, incM, Matrix.fromBlocks_map, Matrix.map_neg]
  have key : incM F (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ) =
      (incM F d.b.1)ᵀ * incM F (dbl d.Y.J) * incM F (d.b.1.map σ) := by
    simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  rw [e1, e2, ← key, h]
  ext (i | i) (j | j)
  · simp [incM, Jm]
  · by_cases hij : i = j
    · subst hij; simp [incM, Jm]
    · simp [incM, Jm, Matrix.one_apply_ne hij]
  · by_cases hij : i = j
    · subst hij; simp [incM, Jm, map_intCast]
    · simp [incM, Jm, Matrix.one_apply_ne hij]
  · simp [incM, Jm]
theorem sub_form_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (c : AE F E →+* AE F E) (ε : AE F E)
    (M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))
    (hr : ∀ b, b ≠ Sum.inr L.i₀ → M (Sum.inr L.i₀) b = 0) :
    (M.submatrix (Sum.map L.em L.em) (Sum.map L.em L.em))ᵀ * Jm L.n ε *
        (M.submatrix (Sum.map L.em L.em) (Sum.map L.em L.em)).map c =
      (Mᵀ * Jm d.n ε * M.map c).submatrix (Sum.map L.em L.em) (Sum.map L.em L.em) := by
  ext x y
  rw [Matrix.submatrix_apply, form_apply, form_apply]
  have hx : Sum.map L.em L.em x ≠ Sum.inr L.i₀ := by
    rcases x with x | x
    · simp
    · simpa using (L.rng (L.em x)).2 ⟨x, rfl⟩
  have hy : Sum.map L.em L.em y ≠ Sum.inr L.i₀ := by
    rcases y with y | y
    · simp
    · simpa using (L.rng (L.em y)).2 ⟨y, rfl⟩
  refine Fintype.sum_of_injective L.em L.inj _ _ (fun k hk => ?_) (fun k => rfl)
  have : k = L.i₀ := by by_contra h; exact hk ((L.rng k).1 h)
  subst this
  rw [hr _ hx, hr _ hy, map_zero]; ring
theorem sub_J_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (ε : AE F E) :
    (Jm d.n ε).submatrix (Sum.map L.em L.em) (Sum.map L.em L.em) = Jm L.n ε := by
  ext (i | i) (j | j) <;> simp [Jm, Matrix.one_apply, L.inj.eq_iff]
theorem mkG_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ)
    (hf : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ) = Jm d.n ((ε : ℤ) : AE F E))
    (N : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))
    (hN : Nᵀ * Jm d.n ((ε : ℤ) : AE F E) * N.map (cA σ).toRingHom = Jm d.n ((ε : ℤ) : AE F E)) :
    ∃ g : d.G, inFrame d.b g = N := by
  set J := Jm d.n ((ε : ℤ) : AE F E) with hJdef
  have hNu : IsUnit N.det := by
    have e : Nᵀ * (J * N.map (cA σ).toRingHom * (((ε : ℤ) : AE F E) • J)) = 1 := by
      calc Nᵀ * (J * N.map (cA σ).toRingHom * (((ε : ℤ) : AE F E) • J))
          = (Nᵀ * J * N.map (cA σ).toRingHom) * (((ε : ℤ) : AE F E) • J) := by simp only [Matrix.mul_assoc]
        _ = J * (((ε : ℤ) : AE F E) • J) := by rw [hN]
        _ = 1 := Jm_sq d.n ε
    have := congrArg Matrix.det e
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
    exact isUnit_iff_exists_inv.2 ⟨_, this⟩
  have hBm : IsUnit (incM F d.b.1) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d, Matrix.det_one]⟩)
  have hBi : IsUnit (incM F (d.b⁻¹).1) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.det_one]⟩)
  have hM0u : IsUnit (incM F d.b.1 * N * incM F (d.b⁻¹).1) :=
    (hBm.mul ((Matrix.isUnit_iff_isUnit_det _).2 hNu)).mul hBi
  have hf' : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ).toRingHom = J := hf
  rw [← hf'] at hN
  have hM0mem := KWhit.form_conj_out (cA σ).toRingHom (_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d) hN
  let u : GL (Fin d.n ⊕ Fin d.n) (AE F E) := hM0u.unit
  have hu : (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) =
      incM F d.b.1 * N * incM F (d.b⁻¹).1 := IsUnit.unit_spec hM0u
  have hmem : u ∈ UG (cA σ) (dbl (incM F d.Y.J)) := by
    show (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))ᵀ * dbl (incM F d.Y.J) *
      (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)).map (cA σ) = dbl (incM F d.Y.J)
    rw [hu]
    exact hM0mem
  refine ⟨⟨u, hmem⟩, ?_⟩
  show incM F (d.b⁻¹).1 * (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) * incM F d.b.1 = N
  rw [hu]
  simp only [← Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.one_mul]
  rw [Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.mul_one]
theorem q_split'_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (ε : ℤˣ)
    (hd : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (hL : L.b.1ᵀ * dbl L.Y.J * L.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (p : d.G) (lam : (AE F E)ˣ)
    (hp : ∀ a, inFrame d.b p a (Sum.inl L.i₀) = if a = Sum.inl L.i₀ then (lam : AE F E) else 0) :
    ∃ g : L.sd.G, IsQ F E L.i₀ (inFrame d.b (p * (L.j g)⁻¹)) lam := by
  set M := inFrame d.b p with hMdef
  have hfd := _root_.PositivityTheory.SiegelWeilFormula.Avac.frame_formE_k d ε hd
  have hfL := _root_.PositivityTheory.SiegelWeilFormula.Avac.frame_formE_k L.sd ε hL
  have hMform : Mᵀ * Jm d.n ((ε : ℤ) : AE F E) * M.map (cA σ).toRingHom = Jm d.n ((ε : ℤ) : AE F E) := by
    have hP : (mat2 p)ᵀ * dbl (incM F d.Y.J) * (mat2 p).map (cA σ).toRingHom = dbl (incM F d.Y.J) := p.2
    have := KWhit.form_conj_in (cA σ).toRingHom (_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d) hP
    have hfd' : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ).toRingHom =
        Jm d.n ((ε : ℤ) : AE F E) := hfd
    rw [hfd'] at this
    exact this
  have hrow := row_zero (cA σ).toRingHom ε hMform hp
  have hsub := _root_.PositivityTheory.SiegelWeilFormula.Avac.sub_form_k L (cA σ).toRingHom (((ε : ℤ) : AE F E)) M hrow
  rw [hMform, _root_.PositivityTheory.SiegelWeilFormula.Avac.sub_J_k] at hsub
  obtain ⟨g, hg⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.mkG_k L.sd ε hfL _ hsub
  refine ⟨g, ?_⟩
  rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k, ← map_inv]
  set H' := inFrame d.b (L.j g⁻¹) with hH'
  have hI : IdI (I0 L.i₀) H' := _root_.PositivityTheory.SiegelWeilFormula.Avac.idI_j_k L g⁻¹
  have hsubH : H'.submatrix (Sum.map L.em L.em) (Sum.map L.em L.em) = inFrame L.b g⁻¹ := L.j_in g⁻¹
  have hinv : M.submatrix (Sum.map L.em L.em) (Sum.map L.em L.em) * inFrame L.b g⁻¹ = 1 := by
    have e := _root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k L.sd g g⁻¹
    rw [mul_inv_cancel, _root_.PositivityTheory.SiegelWeilFormula.Avac.inFrame_one_k] at e
    rw [← hg]; exact e.symm
  refine ⟨fun a b ha hb => ?_, fun a => ?_, fun b hb => ?_⟩
  · obtain ⟨a', rfl⟩ := (_root_.PositivityTheory.SiegelWeilFormula.Avac.emm_rng_k L a).1 ha
    obtain ⟨b', rfl⟩ := (_root_.PositivityTheory.SiegelWeilFormula.Avac.emm_rng_k L b).1 hb
    have e := congrFun (congrFun (hI.sub_mul_right M (_root_.PositivityTheory.SiegelWeilFormula.Avac.emm_inj_k L) (_root_.PositivityTheory.SiegelWeilFormula.Avac.emm_rng_k L)) a') b'
    rw [Matrix.submatrix_apply, hsubH, hinv] at e
    rw [e]
    by_cases hab : a' = b'
    · subst hab; simp
    · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne ((_root_.PositivityTheory.SiegelWeilFormula.Avac.emm_inj_k L).ne hab)]
  · rw [mul_col_one (fun v => (hI _ (Or.inl rfl) v).2)]
    exact hp a
  · rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inr L.i₀)]
    · rw [(hI _ (Or.inr rfl) b).1, Matrix.one_apply_ne (Ne.symm hb), mul_zero]
    · intro c _ hc
      rw [show inFrame d.b p (Sum.inr L.i₀) c = 0 from hrow c hc, zero_mul]
    · simp
end PositivityTheory.SiegelWeilFormula.Avac
end
end
end
