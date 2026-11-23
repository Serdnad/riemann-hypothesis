module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle063
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle064
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle049
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle055
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle096
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle069
import GroundTheory.HeightsAndTheta.Heights.Intersections.PTorusInvLevi
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle068
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle100
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle092
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimeGermPrimitivePresentation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle002
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem LelongMassNearSmall.proof (hReg : RegMassNearSmall.Statement)
    (hVar : VarMassNearSmall.Statement) : LelongMassNearSmall.Statement := by
  classical
  intro n d J I u φ f hJ hdim hu hφ _ hIdim hf hfc δ hδ
  set S := (J ⊔ Ideal.span {linForm u}).minimalPrimes with hS
  have hSfin : S.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  set M : ℝ := ∑ W ∈ hSfin.toFinset, (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun W _ => Nat.cast_nonneg _
  have hδ' : 0 < δ / (M + 1) := by positivity
  obtain ⟨U₀, hU₀, hIU₀, hT⟩ := hReg n d J I u φ f hJ hdim hu hφ hIdim hf.continuous hfc δ hδ
  have hW : ∀ W ∈ S, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ zeroSet I ⊆ U ∧
      ∀ χ : (Fin n → ℂ) → ℝ, Continuous χ → (∀ x, |χ x| ≤ 1) → tsupport χ ⊆ U →
        |varInt W d (fun x => χ x * f x) φ| ≤ δ / (M + 1) := by
    intro W hWm
    obtain ⟨hWp, hWJ, -⟩ := mem_minimalPrimes_sup_linForm hWm
    refine hVar n d W I φ f hWp
      (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.dim_component_linForm hJ hdim hu hWm)
      (fun i => ?_) hIdim hf.continuous hfc _ hδ'
    obtain ⟨U, hU, hSU, hC⟩ := hφ i
    exact ⟨U, hU, hWJ.trans hSU, hC⟩
  choose! UW hUW hIUW hLW using hW
  have hU : IsOpen (U₀ ∩ ⋂ W ∈ S, UW W) :=
    hU₀.inter (hSfin.isOpen_biInter fun W hW => hUW W hW)
  have hIU : zeroSet I ⊆ U₀ ∩ ⋂ W ∈ S, UW W :=
    Set.subset_inter hIU₀ (Set.subset_iInter₂ fun W hW => hIUW W hW)
  obtain ⟨χ, hχ, hχ01, hχU, V, hV, hIV, hχ1⟩ := exists_cutoff_near_zeroSet I hU hIU
  have hχb : ∀ x, |χ x| ≤ 1 := fun x => abs_le.2 ⟨by linarith [(hχ01 x).1], (hχ01 x).2⟩
  refine ⟨χ, hχ, ⟨V, hV, hIV, hχ1⟩, ?_, ?_⟩
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
    exact hT χ hχ.continuous hχb (hχU.trans Set.inter_subset_left) ε ⟨hε.1, hε.2.le⟩
  · rw [finsum_mem_eq_finite_toFinset_sum _ hSfin]
    calc |∑ W ∈ hSfin.toFinset, (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) *
            varInt W d (fun x => χ x * f x) φ|
        ≤ ∑ W ∈ hSfin.toFinset, (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * (δ / (M + 1)) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun W hW => ?_)
          have hWS : W ∈ S := hSfin.mem_toFinset.1 hW
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
          exact mul_le_mul_of_nonneg_left (hLW W hWS χ hχ.continuous hχb
            (hχU.trans (Set.inter_subset_right.trans (Set.biInter_subset_of_mem hWS))))
            (Nat.cast_nonneg _)
      _ = M * (δ / (M + 1)) := by rw [← Finset.sum_mul]
      _ ≤ δ := by
          rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
          nlinarith

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix ComplexSets
open GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
open scoped ComplexOrder

noncomputable section

namespace RegularizedLogDensityNonneg

theorem hessC_logDistSq_comp_posSemidef {n e : ℕ} (x : Fin n → ℂ) (s : (Fin e → ℂ) → Fin n → ℂ)
    (y : Fin e → ℂ) (han : AnalyticAt ℂ s y) (hne : s y ≠ x) :
    (ReciprocityTheory.AnForm.hessC (logDistSq x ∘ s) y).PosSemidef := by
  let τ : (Fin e → ℂ) → Fin n → ℂ := fun w => s w - x
  have hτ : AnalyticAt ℂ τ y := han.sub analyticAt_const
  have hS : sqSum (τ y) ≠ 0 := by
    intro h0
    apply hne
    have hj : ∀ j ∈ Finset.univ, ‖(s y - x) j‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg _).1 h0
    funext j
    have := hj j (Finset.mem_univ j)
    simpa [sub_eq_zero] using this
  have hφ : ContDiffAt ℝ 2 phi (τ y) := contDiffAt_phi hS
  have hfun : logDistSq x ∘ s = fun w => 2 * (phi ∘ τ) w := by
    funext w
    simp only [Function.comp_apply, logDistSq, phi, τ, euclPot, sqSum]
    ring
  have hP : (ReciprocityTheory.AnForm.hessC (phi ∘ τ) y).PosSemidef := by
    refine ReciprocityTheory.AnForm.M.hessC_posSemidef _ _ (hφ.comp _ hτ.restrictScalars.contDiffAt) fun v => ?_
    rw [ReciprocityTheory.AnForm.levi_comp v hτ hφ]
    exact GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi.leviForm_phi_nonneg hS _
  rw [hfun, ReciprocityTheory.AnForm.M.hessC_const_mul']
  exact hP.smul (by norm_num)

end RegularizedLogDensityNonneg

theorem RegLogDensNonneg.proof : RegLogDensNonneg.Statement := by
  intro n d J A u ε x z s hε hzx hs
  have han : AnalyticAt ℂ s (A *ᵥ z) := FormIntegralPositivity.analyticAt_sheet hs
  have hsz : s (A *ᵥ z) = z := by
    obtain ⟨U, -, -, -, h, -⟩ := hs
    exact h
  refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun k => ?_
  refine Fin.cases ?_ (fun j => ?_) k
  · simp only [Matrix.cons_val_zero]
    set y := A *ᵥ z
    have hh : AnalyticAt ℂ (fun w => linEval u (s w)) y := by
      unfold linEval
      exact Finset.analyticAt_fun_sum _ fun j _ => analyticAt_const.mul ((analyticAt_pi_iff.1 han) j)
    let τ : (Fin (d + 1) → ℂ) → (Fin 2 → ℂ) := fun w => ![linEval u (s w), ((√ε : ℝ) : ℂ)]
    have hτ : AnalyticAt ℂ τ y := by
      refine analyticAt_pi_iff.2 fun i => ?_
      fin_cases i
      · simpa [τ] using hh
      · simpa [τ] using (analyticAt_const : AnalyticAt ℂ (fun _ : Fin (d + 1) → ℂ => ((√ε : ℝ) : ℂ)) y)
    have hS : sqSum (τ y) ≠ 0 := by
      have : sqSum (τ y) = ‖linEval u (s y)‖ ^ 2 + ε := by
        simp only [τ, sqSum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hε.le]
      rw [this]
      positivity
    have hφ : ContDiffAt ℝ 2 phi (τ y) := contDiffAt_phi hS
    have hfun : logReg u ε ∘ s = phi ∘ τ := by
      funext w
      exact RegularizedDensityNonneg.half_log_eq_phi _ hε.le
    rw [hfun]
    refine ReciprocityTheory.AnForm.M.hessC_posSemidef _ _ (hφ.comp _ hτ.restrictScalars.contDiffAt) fun v => ?_
    rw [ReciprocityTheory.AnForm.levi_comp v hτ hφ]
    exact GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi.leviForm_phi_nonneg hS _
  · simp only [Matrix.cons_val_succ]
    exact RegularizedLogDensityNonneg.hessC_logDistSq_comp_posSemidef x s _ han (hsz.symm ▸ hzx)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology ComplexSets

noncomputable section

theorem DivisorRegularGeneric.proof (hG : FrameGraphGeneric.Statement) : DivisorRegularGeneric.Statement := by
  classical
  intro n d J u hJ hdim hu
  set L : Ideal (MvPolynomial (Fin n) ℂ) := J ⊔ Ideal.span {linForm u} with hL
  have hfinM : L.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ L
  set T := hfinM.toFinset with hT
  have hmemT : ∀ W, W ∈ T ↔ W ∈ L.minimalPrimes := fun W => hfinM.mem_toFinset
  have hevL : ∀ x : Fin n → ℂ, eval x (linForm u) = linEval u x := fun x => by

    simp [linForm, linEval, map_sum]

  have hdimW : ∀ W ∈ L.minimalPrimes, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) := by
    intro W hW
    have key := ringKrullDim_quotient_minimalPrime_add_one hu hW (fun h => by
      rw [hdim] at h
      exact ENat.natCast_ne_top _ (WithBot.coe_injective h))
    rw [hdim] at key
    exact ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_withBot_eq_of_add_one key
  choose! hh hhW hhchart using fun W (hW : W ∈ L.minimalPrimes) =>
    graphChart_of_frameGraphGeneric hG W hW.1.1 (hdimW W hW)

  have hsep : ∀ W ∈ L.minimalPrimes, ∀ V ∈ L.minimalPrimes, W ≠ V → ∃ g ∈ V, g ∉ W := by
    intro W hW V hV hne
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm (hW.2 hV.1 hcon) hcon)
  choose! gg hggV hggW using hsep
  set e : Ideal (MvPolynomial (Fin n) ℂ) → MvPolynomial (Fin n) ℂ := fun W => ∏ V ∈ T.erase W, gg W V with he
  have heW : ∀ W ∈ L.minimalPrimes, e W ∉ W := by
    intro W hW hmem
    have : W.IsPrime := hW.1.1
    obtain ⟨V, hV, hgV⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hggW W hW V ((hmemT V).mp (Finset.mem_of_mem_erase hV)) (Finset.ne_of_mem_erase hV).symm hgV
  have heV : ∀ W ∈ L.minimalPrimes, ∀ V ∈ L.minimalPrimes, W ≠ V → e W ∈ V := by
    intro W hW V hV hne
    have : V.IsPrime := hV.1.1
    exact Ideal.IsPrime.prod_mem_iff.mpr
      ⟨V, Finset.mem_erase.mpr ⟨hne.symm, (hmemT V).mpr hV⟩, hggV W hW V hV hne⟩
  set f : MvPolynomial (Fin n) ℂ := ∑ W ∈ T, hh W * e W with hf
  have hsplit : ∀ W ∈ T, f = hh W * e W + ∑ V ∈ T.erase W, hh V * e V := fun W hW =>
    (Finset.add_sum_erase T _ hW).symm
  have hrest : ∀ W ∈ L.minimalPrimes, ∑ V ∈ T.erase W, hh V * e V ∈ W := by
    intro W hW
    refine Ideal.sum_mem _ fun V hV => Ideal.mul_mem_left _ _ ?_
    exact heV V ((hmemT V).mp (Finset.mem_of_mem_erase hV)) W hW (Finset.ne_of_mem_erase hV)
  have hfW : ∀ W ∈ L.minimalPrimes, f ∉ W := by
    intro W hW hmem
    rw [hsplit W ((hmemT W).mpr hW), Ideal.add_mem_iff_left _ (hrest W hW)] at hmem
    rcases hW.1.1.mem_or_mem hmem with h | h
    · exact hhW W hW h
    · exact heW W hW h

  have hcomp : ∀ x ∈ zeroSet J, linEval u x = 0 → ∃ W ∈ L.minimalPrimes, x ∈ zeroSet W := by
    intro x hxJ hxu
    have hxL : L ≤ RingHom.ker (eval x) := sup_le (fun p hp => RingHom.mem_ker.mpr (hxJ p hp))
      (Ideal.span_le.mpr (by simpa [hevL] using hxu))
    have : (RingHom.ker (eval x)).IsPrime := RingHom.ker_isPrime _
    obtain ⟨W, hW, hWx⟩ := Ideal.exists_minimalPrimes_le hxL
    exact ⟨W, hW, fun p hp => RingHom.mem_ker.mp (hWx hp)⟩
  have hcompInv : ∀ W ∈ L.minimalPrimes, ∀ x ∈ zeroSet W, x ∈ zeroSet J ∧ linEval u x = 0 := by
    intro W hW x hx
    refine ⟨fun p hp => hx p (hW.1.2 (Ideal.mem_sup_left hp)), ?_⟩
    rw [← hevL]
    exact hx _ (hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
  refine ⟨L ⊔ Ideal.span {f}, le_sup_left, ringKrullDim_quotient_sup_span_lt hfW hdimW, ?_⟩
  intro q hqJ hqu hqI
  obtain ⟨W, hW, hqW⟩ := hcomp q hqJ hqu
  have hfq : eval q f ≠ 0 := by
    intro h0
    refine hqI fun p hp => ?_
    have hle : L ⊔ Ideal.span {f} ≤ RingHom.ker (eval q) := by
      refine sup_le (fun p hp => ?_) (Ideal.span_le.mpr (by simpa using h0))
      obtain ⟨V, hV, hqV⟩ := hcomp q hqJ hqu
      exact RingHom.mem_ker.mpr (hqV p (hV.1.2 hp))
    exact RingHom.mem_ker.mp (hle hp)
  rw [hsplit W ((hmemT W).mpr hW), map_add (f := _), hqW _ (hrest W hW), add_zero, map_mul] at hfq
  refine graphChart_of_eq_on_open (U := {x | eval x (e W) ≠ 0})
    (isOpen_ne_fun (MvPolynomial.continuous_eval _) continuous_const) (right_ne_zero_of_mul hfq) ?_
    (hhchart W hW q hqW (left_ne_zero_of_mul hfq))
  ext x
  constructor
  · rintro ⟨⟨hxJ, hxu⟩, hxe⟩
    refine ⟨?_, hxe⟩
    obtain ⟨V, hV, hxV⟩ := hcomp x hxJ hxu
    by_cases hVW : V = W
    · exact hVW ▸ hxV
    · exact absurd (hxV _ (heV W hW V hV (Ne.symm hVW))) hxe
  · rintro ⟨hxW, hxe⟩
    exact ⟨hcompInv W hW x hxW, hxe⟩

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter PrimeGermPrimitivePresentation

noncomputable section

namespace GermProjectionFunctionForm

variable {σ : Type} [Fintype σ]

theorem germPull_toGerm {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (w : σ → ℂ) (u : anFun (A w)) :
    germPull A (A.analyticAt w) rfl (toGerm (A w) u) = toGerm w (compA A w u) :=
  Subtype.ext (germPull_coe A (A.analyticAt w) rfl _ u.1 rfl)

theorem coordGerm_eq_toGerm (w : σ → ℂ) (i : σ) :
    coordGerm w i = toGerm w (mkA (fun z : σ → ℂ => z i)
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt w)) :=
  Subtype.ext rfl

theorem isGermCombination_of_mem {w : σ → ℂ} {k : ℕ} (p : Fin k → (σ → ℂ) → ℂ) (u : anFun w)
    (hu : toGerm w u ∈ holGermIdeal w p) (f : (σ → ℂ) → ℂ) (hf : ∀ z, u.1 z = f z) :
    IsGermCombination w p f := by
  obtain ⟨h, hh, e⟩ := exists_of_mem_holGermIdeal p hu
  exact ⟨h, hh, (Germ.coe_eq.1 e).mono fun z hz => by rw [← hf]; exact hz⟩

end GermProjectionFunctionForm


open GermProjectionFunctionForm in
theorem GermProjectionFunctionForm.proof : GermProjectionFunctionForm.Statement := by
  classical
  intro σ _ w k p d A hp ⟨hinj, hgen, hint⟩
  let Z : σ → anFun w := fun i => mkA (fun z : σ → ℂ => z i)
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt w)
  have hZ : ∀ i, coordGerm w i = toGerm w (Z i) := coordGerm_eq_toGerm w
  have hpull : ∀ φ : holGerms (A w), germPull A (A.analyticAt w) rfl φ = toGerm w (compA A w (rep φ)) := by
    intro φ
    conv_lhs => rw [← toGerm_rep φ]
    exact germPull_toGerm A w (rep φ)
  refine ⟨?_, ?_, ?_⟩
  · intro h hh hcomb
    have hmem := (toGerm_mem_iff hp (compA A w (mkA h hh))).2 hcomb
    rw [← germPull_toGerm] at hmem
    have h0 := congrArg Subtype.val (hinj _ hmem)
    exact Germ.coe_eq.1 (h0.trans (Germ.coe_zero (l := 𝓝 (A w)) (M := ℂ)).symm)
  · intro i
    obtain ⟨q, hq, hqP⟩ := hint i
    refine ⟨q.natDegree, fun j => (rep (q.coeff j)).1, fun j => (rep (q.coeff j)).2, ?_⟩
    have key : q.eval₂ (germPull A (A.analyticAt w) rfl) (coordGerm w i) =
        toGerm w (Z i ^ q.natDegree + ∑ j : Fin q.natDegree, compA A w (rep (q.coeff j)) * Z i ^ (j : ℕ)) := by
      conv_lhs => rw [hq.as_sum]

      simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_finsetSum,
      Polynomial.eval₂_mul, Polynomial.eval₂_C, map_add, map_pow, map_sum, map_mul, hpull, hZ]
      rw [Fin.sum_univ_eq_sum_range (fun j => toGerm w (compA A w (rep (q.coeff j))) * toGerm w (Z i) ^ j)]
    rw [key] at hqP
    refine isGermCombination_of_mem p _ hqP _ fun z => ?_
    simp [Z, mkA, compA, Finset.sum_apply]
  · intro g hg
    obtain ⟨F, hF⟩ := hgen (toGerm w (mkA g hg))
    let e := Finsupp.equivFunOnFinite (α := σ) (M := ℕ)
    refine ⟨F.support.image e, fun m => (rep (F.coeff (e.symm m))).1, fun m _ => (rep (F.coeff (e.symm m))).2, ?_⟩
    have key : toGerm w (mkA g hg) - MvPolynomial.eval₂ (germPull A (A.analyticAt w) rfl) (coordGerm w) F =
        toGerm w (mkA g hg - ∑ m ∈ F.support, compA A w (rep (F.coeff m)) * ∏ i, Z i ^ m i) := by
      rw [MvPolynomial.eval₂_eq']

      simp only [map_sub, map_sum, map_mul, map_prod, map_pow, hpull, hZ]
    rw [key] at hF
    refine isGermCombination_of_mem p _ hF _ fun z => ?_
    rw [Finset.sum_image (fun x _ y _ h => e.injective h)]
    simp [Z, mkA, compA, Finset.sum_apply, Finset.prod_apply, e]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
