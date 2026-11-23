module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.Smoothing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Bundle006
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.HahnBanach
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic


theorem pf_GFin : GFin := by
  intro hSHt hSm hRS hRE hRL hRD hRLip hTh hPr hBu hNr hDB
  intro L _ _ hTC
  refine ⟨1, fun N hN => ?_⟩
  obtain ⟨μ, hμ⟩ := hSm L N hN
  obtain ⟨cL, hcL, hL⟩ := hRL L N hN μ hμ
  obtain ⟨cD, hcD, hD⟩ := hRD L hTC N hN μ hμ
  obtain ⟨K, hKc, hKP, hKt⟩ := hTh L hTC N hN (min cL cD) (lt_min hcL hcD)
  obtain ⟨ψ, K', Cψ, hK'c, hK'P, hψ, hψsupp, hψb, hψsum, hψlip⟩ := hBu L N K hKc hKP
  obtain ⟨nf, Cn, hCn, hnS, hnt, hnEq, hnH, hnLL, hnLip⟩ := hNr L N hN
  obtain ⟨Cr, hCr, hrLip⟩ := hRLip L N hN μ hμ
  obtain ⟨c0, hc0, hc0le⟩ := (hSHt L hTC N hN).2.2.1
  have hPopen : IsOpen (Pos L N) := (hPr L N).1
  have hcone : ∀ t : ℝ, 0 < t → ∀ h ∈ Pos L N, t • h ∈ Pos L N := by
    intro t ht h hh
    unfold Pos at hh ⊢
    intro w
    have e : mat (t • h) w = t • mat h w := by simp
    rw [e]
    exact (hh w).smul ht
  have hnP : ∀ h ∈ Pos L N, nf h ∈ Pos L N := by
    intro h hh
    obtain ⟨t, ht, e⟩ := hnt h hh
    rw [e]
    exact hcone t ht h hh
  have hFP : ∀ h ∈ Pos L N, ret μ (nf h) ∈ Pos L N := fun h hh =>
    (hRE L N hN μ hμ (nf h) (hnP h hh)).2.1
  have hFeq : ∀ γ : Gm L N, ∀ h ∈ Pos L N, ret μ (nf (ac γ h)) = ac γ (ret μ (nf h)) := by
    intro γ h hh
    rw [hnEq γ h hh, (hRE L N hN μ hμ (nf h) (hnP h hh)).1 γ]
  have hinv : ∀ (γ : Gm L N) (h : HS L N), actL ((emb L N) γ)⁻¹ h = ac γ⁻¹ h := by
    intro γ h
    rw [← map_inv]
  have hretS : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ret μ) (Pos L N) := hRS L N hN μ hμ
  have hFS : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun h => ret μ (nf h)) (Pos L N) :=
    hretS.comp hnS (fun h hh => hnP h hh)
  have hFc : ContinuousOn (fun h => ret μ (nf h)) (Pos L N) := hFS.continuousOn
  have hφS : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun h => ψ (ret μ (nf h))) (Pos L N) :=
    hψ.comp_contDiffOn hFS
  have hCψ : 0 ≤ Cψ := (abs_nonneg _).trans (hψb 0)
  refine ⟨⟨fun h => ψ (ret μ (nf h)), hφS, ?_, ?_, ?_, ?_, ⟨Cψ, fun h _ => hψb _⟩, ?_⟩⟩
  · intro h0
    obtain ⟨V, hV, hV0, hVP⟩ := exists_compact_subset hPopen h0.2
    have hW : IsCompact ((fun h => ret μ (nf h)) '' V) := hV.image_of_continuousOn (hFc.mono hVP)
    have hWP : (fun h => ret μ (nf h)) '' V ⊆ Pos L N := by
      rintro _ ⟨y, hy, rfl⟩
      exact hFP y (hVP hy)
    have hfin := (hPr L N).2 _ (hW.union hK'c) (Set.union_subset hWP hK'P)
    refine ⟨Subtype.val ⁻¹' interior V,
      continuous_subtype_val.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hV0), ?_⟩
    refine (hfin.preimage inv_injective.injOn).subset ?_
    rintro γ ⟨h, hS, hU⟩
    have hk := hψsupp _ hS
    rw [hinv, hFeq _ _ h.2] at hk
    exact ⟨_, Or.inl ⟨h, interior_subset hU, rfl⟩, Or.inr hk⟩
  · intro h hh
    have h1 : min cL cD ≤ lam (ret μ (nf h)) := (min_le_left cL cD).trans (hL (nf h) (hnP h hh))
    have h2 : min cL cD ≤ lamD (ret μ (nf h)) := (min_le_right cL cD).trans (hD (nf h) (hnP h hh))
    obtain ⟨γ0, hγ0⟩ := hKt (ret μ (nf h)) (hFP h hh) h1 h2
    rw [← hψsum (ret μ (nf h)) (hFP h hh) ⟨γ0, hγ0⟩]
    refine finsum_congr fun γ => ?_
    rw [hinv, hinv, hFeq _ _ hh]
  · have hcl : closure {k : ↑(Pos L N) | ψ (ret μ (nf ↑k)) ≠ 0} ⊆
        {k : ↑(Pos L N) | ret μ (nf ↑k) ∈ K'} := by
      apply closure_minimal
      · intro k hk
        exact hψsupp _ hk
      · exact hK'c.isClosed.preimage hFc.restrict
    refine (((hPr L N).2 K' hK'c hK'P).preimage inv_injective.injOn).subset ?_
    rintro γ ⟨h, hh, hg⟩
    have a := hcl hh
    have b := hcl hg
    simp only [Set.mem_setOf_eq] at a b
    change ret μ (nf (actL ((emb L N) γ)⁻¹ ↑h)) ∈ K' at b
    rw [hinv, hFeq _ _ h.2] at b
    exact ⟨_, a, b⟩
  · intro r hr h hh
    simp only [hnH r hr h hh]
  · refine ⟨(N : ℝ) * (Cψ * Cr * Cn * (1 + c0⁻¹)), fun x => ?_⟩
    have h0P : actL x ↑(one L N) ∈ Pos L N := (x • one L N).2
    obtain ⟨t, htp, et⟩ := hnt _ h0P
    have hprod : lam (nf (actL x ↑(one L N))) * lamD (nf (actL x ↑(one L N))) =
        lam (actL x ↑(one L N)) * lamD (actL x ↑(one L N)) := by
      rw [et]
      exact hnLL t htp _ h0P
    have hhtx : (lam (actL x ↑(one L N)) * lamD (actL x ↑(one L N)))⁻¹ = ht x := rfl
    have hx0 : c0 ≤ ht x := hc0le x
    have hxnn : 0 ≤ ht x := hc0.le.trans hx0
    have hB : 0 ≤ Cψ * Cr * (1 + ht x) * Cn :=
      mul_nonneg (mul_nonneg (mul_nonneg hCψ hCr) (by linarith)) hCn
    have hε : (0 : ℝ) < 1 / (4 * (Cn + 1)) := by positivity
    have hdiff : DifferentiableAt ℝ (fun h => ψ (ret μ (nf h))) (actL x ↑(one L N)) :=
      (hφS.contDiffAt (hPopen.mem_nhds h0P)).differentiableAt (by simp)
    have key := hDB L N (fun h => ψ (ret μ (nf h))) x (Cψ * Cr * (1 + ht x) * Cn)
      (1 / (4 * (Cn + 1))) hB hε hdiff (by
        intro δ hδ0 hδε k hk
        have hm : δ * (4 * (Cn + 1)) ≤ 1 := by
          rw [le_div_iff₀ (by positivity)] at hδε
          exact hδε
        have hδ4 : δ ≤ 1 / 4 := by nlinarith
        have hCnδ : Cn * δ ≤ 1 / 4 := by nlinarith
        have c1 := hnLip δ hδ0 hδ4 _ h0P k hk
        have c2 := hrLip (Cn * δ) (mul_nonneg hCn hδ0) hCnδ _ (hnP _ h0P) (nf k) c1
        rw [hprod, hhtx] at c2
        have c3 := hψlip _ (mul_nonneg (mul_nonneg hCr (by linarith))
          (mul_nonneg hCn hδ0)) _ (hFP _ h0P) _ c2
        exact le_of_le_of_eq c3 (by ring))
    show _ ≤ _ * ht x ^ 1
    rw [pow_one]
    have e1 : 1 ≤ c0⁻¹ * ht x := by
      rw [inv_mul_eq_div, le_div_iff₀ hc0]
      linarith
    have e2 : 1 + ht x ≤ (1 + c0⁻¹) * ht x := by nlinarith
    have hK0 : 0 ≤ (N : ℝ) * (Cψ * Cr * Cn) :=
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg hCψ hCr) hCn)
    calc _ ≤ (N : ℝ) * (Cψ * Cr * (1 + ht x) * Cn) := key
      _ = (N : ℝ) * (Cψ * Cr * Cn) * (1 + ht x) := by ring
      _ ≤ (N : ℝ) * (Cψ * Cr * Cn) * ((1 + c0⁻¹) * ht x) := mul_le_mul_of_nonneg_left e2 hK0
      _ = _ := by ring

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
end

section

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

private theorem emb_val (γ : Gm L N) (w : InfinitePlace L) :
    ((emb L N γ w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      (γ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) := by
  ext i j
  rfl

private theorem act_inj (γ : Gm L N) : Function.Injective (actL (emb L N γ) : HS L N → HS L N) := by
  intro a b hab
  have e := congrArg (actL (emb L N γ)⁻¹) hab
  rwa [← actL_mul, ← actL_mul, inv_mul_cancel, actL_one, actL_one] at e

private theorem inj_finsum {ι : Type} (f : HS L N →L[ℝ] HS L N) (hf : Function.Injective f)
    (g : ι → HS L N) : f (∑ᶠ i, g i) = ∑ᶠ i, f (g i) := by
  by_cases h : (Function.support g).Finite
  · exact map_finsum f h
  · have e : (Function.support fun i => f (g i)) = Function.support g := by
      ext i
      simp only [Function.mem_support, ne_eq, map_eq_zero_iff f hf]
    have h' : ¬ (Function.support fun i => f (g i)).Finite := by rwa [e]
    rw [finsum_of_infinite_support h, finsum_of_infinite_support h', map_zero]

private theorem mat_rk (h : HS L N) (v : Lat L N) (w : InfinitePlace L) :
    mat (rk h v) w = vecMulVec (mat h w *ᵥ toR v w) (star (mat h w *ᵥ toR v w)) := rfl

private theorem rk_act (γ : Gm L N) (h : HS L N) (v : Lat L N) :
    rk (actL (emb L N γ) h) (γ • v) = actL (emb L N γ) (rk h v) := by
  refine HS_ext fun w => ?_
  have hv : toR (γ • v) w = ((emb L N γ w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *ᵥ toR v w := by
    rw [smul_lat, toR_mulVec, emb_val]
  have hPA : (((emb L N γ w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *
      ((emb L N γ w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [mat_rk, mat_actL, mat_actL, mat_rk, hv]
  set P := (((emb L N γ w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) with hP
  set A := ((emb L N γ w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) with hA
  have e1 : (Pᴴ * mat h w * P) *ᵥ (A *ᵥ toR v w) = Pᴴ *ᵥ (mat h w *ᵥ toR v w) := by
    calc (Pᴴ * mat h w * P) *ᵥ (A *ᵥ toR v w) = Pᴴ *ᵥ (mat h w *ᵥ ((P * A) *ᵥ toR v w)) := by
          simp only [mulVec_mulVec, Matrix.mul_assoc]
      _ = _ := by rw [hPA, one_mulVec]
  rw [e1, star_mulVec, conjTranspose_conjTranspose, mul_vecMulVec, vecMulVec_mul]

private theorem zed_act (hq : ∀ (γ : Gm L N) (h : HS L N) (v : Lat L N), q (actL (emb L N γ) h) v = q h (γ⁻¹ • v))
    (s : ℝ) (γ : Gm L N) (h : HS L N) : zed s (actL (emb L N γ) h) = zed s h := by
  unfold zed
  rw [← finsum_comp_equiv (MulAction.toPerm γ : Equiv.Perm (Lat L N))
    (f := fun v => rho (q (actL (emb L N γ) h) v / s))]
  refine finsum_congr fun v => ?_
  simp only [MulAction.toPerm_apply, hq, inv_smul_smul]

private theorem sum_act (hq : ∀ (γ : Gm L N) (h : HS L N) (v : Lat L N), q (actL (emb L N γ) h) v = q h (γ⁻¹ • v))
    (s : ℝ) (γ : Gm L N) (h : HS L N) :
    ∑ᶠ v : Lat L N, rho (q (actL (emb L N γ) h) v / s) • rk (actL (emb L N γ) h) v =
      actL (emb L N γ) (∑ᶠ v : Lat L N, rho (q h v / s) • rk h v) := by
  rw [inj_finsum _ (act_inj γ),
    ← finsum_comp_equiv (MulAction.toPerm γ : Equiv.Perm (Lat L N))
      (f := fun v => rho (q (actL (emb L N γ) h) v / s) • rk (actL (emb L N γ) h) v)]
  refine finsum_congr fun v => ?_
  simp only [MulAction.toPerm_apply, hq, inv_smul_smul, rk_act, map_smul]

private theorem term_act (hq : ∀ (γ : Gm L N) (h : HS L N) (v : Lat L N), q (actL (emb L N γ) h) v = q h (γ⁻¹ • v))
    (s : ℝ) (γ : Gm L N) (h : HS L N) : term s (actL (emb L N γ) h) = actL (emb L N γ) (term s h) := by
  unfold term
  rw [zed_act hq, sum_act hq, map_smul]

private theorem ret_act (hq : ∀ (γ : Gm L N) (h : HS L N) (v : Lat L N), q (actL (emb L N γ) h) v = q h (γ⁻¹ • v))
    (μ : HS L N → ℝ) (hμ : Smoothing lamD μ) (γ : Gm L N) {h : HS L N} (hh : h ∈ Pos L N) :
    ret μ (actL (emb L N γ) h) = actL (emb L N γ) (ret μ h) := by
  have hi : μ (actL (emb L N γ) h) = μ h := hμ.inv γ h hh
  unfold ret
  rw [hi, map_add (f := _), map_smul, inj_finsum _ (act_inj γ)]
  congr 1
  exact finsum_congr fun k => by rw [term_act hq, map_smul]

private def Psd (h : HS L N) : Prop := ∀ w, (mat h w).PosSemidef

private theorem psd_rk (h : HS L N) (v : Lat L N) : Psd (rk h v) := fun w => by
  rw [mat_rk]
  exact posSemidef_vecMulVec_self_star _

private theorem psd_add {a b : HS L N} (ha : Psd a) (hb : Psd b) : Psd (a + b) := fun w => by
  rw [mat_add]; exact (ha w).add (hb w)

private theorem psd_smul {a : HS L N} (ha : Psd a) {c : ℝ} (hc : 0 ≤ c) : Psd (c • a) := fun w => by
  rw [mat_smul]; exact (ha w).smul hc

private theorem psd_zero : Psd (0 : HS L N) := fun w => by
  rw [mat_zero]; exact PosSemidef.zero

private theorem psd_finsum {ι : Type} (g : ι → HS L N) (hg : ∀ i, Psd (g i)) : Psd (∑ᶠ i, g i) :=
  finsum_induction Psd psd_zero (fun _ _ => psd_add) hg

private theorem rho_nonneg (x : ℝ) : 0 ≤ rho x := Real.smoothTransition.nonneg _

private theorem psd_term (s : ℝ) (h : HS L N) : Psd (term s h) := by
  unfold term
  refine psd_smul (psd_finsum _ fun v => psd_smul (psd_rk h v) (rho_nonneg _)) ?_
  exact inv_nonneg.2 (mul_nonneg (sq_nonneg s) (finsum_nonneg fun v => rho_nonneg _))

private theorem psd_qR {a : HS L N} (ha : Psd a) (z : VR L N) : 0 ≤ qR a z :=
  Finset.sum_nonneg fun w _ => (Complex.le_def.1 ((ha w).dotProduct_mulVec_nonneg (z w))).1

theorem pf_GREqv : GREqv := by
  intro hB L _ _ N hN μ hμ h hh
  have hq : ∀ (γ : Gm L N) (h : HS L N) (v : Lat L N), q (actL (emb L N γ) h) v = q h (γ⁻¹ • v) :=
    (hB L N hN).2.1
  obtain ⟨c, C, hc, hcmp⟩ := hμ.cmp
  have hD : 0 < lamD h := ((hB L N hN).1 _ ((hB L N hN).1 h hh).2.2.2.1).1
  have hμp : 0 < μ h := lt_of_lt_of_le (mul_pos hc hD) (hcmp h hh).1
  set S := ∑ᶠ k : ℤ, rho ((4 : ℝ) ^ k * μ h) • term ((4 : ℝ) ^ k) h with hSdef
  have hS : Psd S := psd_finsum _ fun k => psd_smul (psd_term _ _) (rho_nonneg _)
  have hr : ret μ h = μ h • h + S := rfl
  refine ⟨fun γ => ret_act hq μ hμ γ hh, fun w => ?_, fun z => ?_⟩
  · rw [hr, mat_add, mat_smul]
    exact ((hh w).smul hμp).add_posSemidef (hS w)
  · have e : qR (μ h • h + S) z = μ h * qR h z + qR S z := by
      simp only [← evR_apply, map_add (f := _), map_smul, smul_eq_mul]
    rw [hr, e]
    linarith [psd_qR hS z]

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
end

section

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL PositivityTheory.KB PositivityTheory.KB.SmoothPartitionUnityBasic.BasicAux
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

private theorem b_qR_single {L : Type} [Field L] [NumberField L] {N : ℕ} [DecidableEq (InfinitePlace L)]
    (h : HS L N) (w : InfinitePlace L) (x : Fin N → ℂ) :
    qR h (Pi.single w x) = (star x ⬝ᵥ (mat h w *ᵥ x)).re := by
  unfold qR
  rw [Finset.sum_eq_single w (fun b _ hb => by rw [Pi.single_eq_of_ne hb]; simp)
    (fun hw => absurd (Finset.mem_univ w) hw), Pi.single_eq_same]

private theorem b_cl_at {L : Type} [Field L] [NumberField L] {N : ℕ} {δ : ℝ} {h k : HS L N}
    (hcl : Cl δ h k) (w : InfinitePlace L) (x : Fin N → ℂ) :
    |(star x ⬝ᵥ (mat k w *ᵥ x)).re - (star x ⬝ᵥ (mat h w *ᵥ x)).re| ≤ δ * (star x ⬝ᵥ (mat h w *ᵥ x)).re := by
  classical
  have := hcl (Pi.single w x)
  rwa [b_qR_single, b_qR_single] at this

private theorem b_toR_ne {L : Type} [Field L] [NumberField L] {N : ℕ} {v : Lat L N} (hv : v ≠ 0) :
    toR v ≠ 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hv
  obtain ⟨w⟩ : Nonempty (InfinitePlace L) := inferInstance
  intro h0
  have := congrFun (congrFun h0 w) a
  simp only [toR, Pi.zero_apply] at this ha
  apply ha
  simpa [embO] using this

private theorem b_qR_pos {L : Type} [Field L] [NumberField L] {N : ℕ} {h : HS L N} (hh : h ∈ Pos L N)
    {z : VR L N} (hz : z ≠ 0) : 0 < qR h z := by
  obtain ⟨c, hc, hev⟩ := UpperTheory.V.KT.lowbd L N h hh
  have h1 := hev.self_of_nhds z
  have : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h2 : 0 < ‖z‖ ^ 2 := by positivity
  nlinarith

private theorem b_emb_val {L : Type} [Field L] [NumberField L] {N : ℕ} (γ : Gm L N) (w : InfinitePlace L) :
    (((emb L N γ) w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      (γ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) := by
  ext i j
  simp [emb, toP, toK, embO, Matrix.GeneralLinearGroup.map_apply]

private theorem b_ginv {L : Type} [Field L] [NumberField L] {N : ℕ} (γ : Gm L N) (w : InfinitePlace L) :
    ((((emb L N γ) w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      ((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) := by
  rw [← b_emb_val, map_inv, Pi.inv_apply]

private theorem b_transp {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) (z : Fin N → ℂ) :
    star z ⬝ᵥ (Mᵀ *ᵥ z) = star (star z) ⬝ᵥ (M *ᵥ star z) := by
  rw [star_star, mulVec_transpose, dotProduct_comm (star z), ← dotProduct_mulVec]

theorem pf_Basic : Basic := by
  intro L _ _ N hN
  classical
  refine ⟨?p1, ?p2, ?p3, ?p4, ?p5, ?p6⟩
  · intro h hh
    have hfin : ∀ B : ℝ, {v : Lat L N | q h v ≤ B}.Finite := fun B => by
      obtain ⟨S, hS, hev⟩ := UpperTheory.V.KT.locfin L N h hh B
      refine hS.subset fun v hv => ?_
      by_contra hvS
      exact absurd hv (not_le.2 (hev.self_of_nhds v hvS))
    have hpos : ∀ v : Lat L N, v ≠ 0 → 0 < q h v := fun v hv => b_qR_pos hh (b_toR_ne hv)
    obtain ⟨v0, hv0⟩ : ∃ v0 : Lat L N, v0 ≠ 0 := by
      refine ⟨Pi.single (⟨0, hN⟩ : Fin N) 1, fun h0 => ?_⟩
      have := congrFun h0 ⟨0, hN⟩
      simp at this
    obtain ⟨vm, ⟨hvm0, -⟩, hvm⟩ := Set.exists_min_image {v : Lat L N | v ≠ 0 ∧ q h v ≤ q h v0}
      (fun v => q h v) ((hfin (q h v0)).subset fun v hv => hv.2) ⟨v0, hv0, le_rfl⟩
    have mlow : ∀ v : Lat L N, v ≠ 0 → q h vm ≤ q h v := fun v hv => by
      by_cases hle : q h v ≤ q h v0
      · exact hvm v ⟨hv, hle⟩
      · exact (hvm v0 ⟨hv0, le_rfl⟩).trans (not_le.1 hle).le
    haveI : Nonempty {y : Lat L N // y ≠ 0} := ⟨⟨v0, hv0⟩⟩
    have hlam : lam h = q h vm := by
      unfold lam
      refine le_antisymm (ciInf_le ⟨q h vm, ?_⟩ (⟨vm, hvm0⟩ : {y : Lat L N // y ≠ 0}))
        (le_ciInf fun y => mlow y.1 y.2)
      rintro _ ⟨y, rfl⟩
      exact mlow y.1 y.2
    refine ⟨by rw [hlam]; exact hpos vm hvm0, fun v hv => by rw [hlam]; exact mlow v hv,
      ⟨vm, hvm0, hlam.symm⟩, fun w => ?_, hfin⟩
    exact (hh w).inv.transpose
  · intro γ h v
    simp only [q, qR, ac, mat_actL, smul_lat, toR_mulVec, b_ginv]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [star_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
  · intro γ
    let γt : Gm L N := ⟨(γ : Matrix (Fin N) (Fin N) (𝓞 L))ᵀ, ((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L))ᵀ,
      by rw [← transpose_mul, Units.inv_mul, transpose_one],
      by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩
    refine ⟨γt⁻¹, fun h hh => HS_ext fun w => ?_⟩
    simp only [dualH, mat_mkHS, ac, mat_actL, b_ginv, inv_inv]
    have hT : ((γt : Matrix (Fin N) (Fin N) (𝓞 L))).map (embO w) =
        ((γ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w))ᵀ := by
      ext i j; rfl
    rw [hT]
    set M := (γ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) with hM
    set G := ((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) with hG
    have hMG : M * G = 1 := by
      rw [hM, hG, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    have hGinv : G⁻¹ = M := Matrix.inv_eq_left_inv hMG
    have hCT : Mᴴᵀ = Mᵀᴴ := by ext i j; simp
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hGinv, ← conjTranspose_nonsing_inv, hGinv,
      transpose_mul, transpose_mul, hCT]
  · intro δ hδ hδ2 h hh k hcl
    have hat := fun w x => b_cl_at hcl w x
    have hk : k ∈ Pos L N := fun w => by
      refine Matrix.PosDef.of_dotProduct_mulVec_pos (mat_herm k w) (by
        intro x hx
        have h1 := (Complex.pos_iff.1 ((hh w).dotProduct_mulVec_pos hx)).1
        have h2 := (abs_le.1 (hat w x)).1
        exact Complex.pos_iff.2 ⟨by nlinarith, (herm_im _ (mat_herm k w) x).symm⟩)
    refine ⟨hk, fun z => ?_⟩
    have per : ∀ w, |(star (z w) ⬝ᵥ (mat (dualH k) w *ᵥ z w)).re -
        (star (z w) ⬝ᵥ (mat (dualH h) w *ᵥ z w)).re| ≤
        2 * δ * (star (z w) ⬝ᵥ (mat (dualH h) w *ᵥ z w)).re := by
      intro w
      simp only [dualH, mat_mkHS]
      rw [b_transp, b_transp]
      have i1 := invmono (mat h w) (mat k w) (hh w) (hk w) (1 - δ) (by linarith)
        (fun x => by have := (abs_le.1 (hat w x)).1; rw [sub_mul, one_mul]; linarith) (star (z w))
      have i2 := invmono (mat k w) (mat h w) (hk w) (hh w) (1 + δ)⁻¹ (by positivity)
        (fun x => by
          rw [inv_mul_le_iff₀ (by linarith)]
          have := (abs_le.1 (hat w x)).2
          rw [add_mul, one_mul]; linarith) (star (z w))
      have hD := re_nonneg_psd (hh w).inv.posSemidef (star (z w))
      have i2' := mul_le_mul_of_nonneg_left i2 (by linarith : (0 : ℝ) ≤ 1 + δ)
      rw [← mul_assoc, mul_inv_cancel₀ (by linarith), one_mul] at i2'
      refine abs_le.2 ⟨by nlinarith [mul_nonneg hδ hD], by nlinarith [mul_nonneg hδ hD]⟩
    unfold qR
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => per w)
  · intro δ hδ h hh k hcl w u v
    have hat := fun x => b_cl_at hcl w x
    have hA : (mat k w - mat h w).IsHermitian := (mat_herm k w).sub (mat_herm h w)
    have hb : ∀ x : Fin N → ℂ, |(star x ⬝ᵥ ((mat k w - mat h w) *ᵥ x)).re| ≤
        δ * (star x ⬝ᵥ (mat h w *ᵥ x)).re := by
      intro x; rw [sub_mulVec, dotProduct_sub, Complex.sub_re]; exact hat x
    have := csq _ _ hA (hh w).posSemidef δ hδ hb u v
    rw [sub_mulVec, dotProduct_sub] at this
    have ha := re_nonneg_psd (hh w).posSemidef u
    have hb' := re_nonneg_psd (hh w).posSemidef v
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg δ) ha) hb']
  · obtain ⟨P, hP⟩ := Submodule.ClosedComplemented.of_finiteDimensional (𝕜 := ℝ) (HSsub L N)
    have hent : ∀ w a b, ContDiff ℝ (⊤ : ℕ∞) (fun h : HS L N => mat h w a b) := fun w a b => by
      have e : (fun h : HS L N => mat h w a b) =
          (fun x : InfinitePlace L → Fin N → Fin N → ℂ => x w a b) ∘ (HSsub L N).subtypeL := rfl
      rw [e]
      exact (contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 contDiff_id w) a) b).comp
        (HSsub L N).subtypeL.contDiff
    have hF : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun h : HS L N => ((dualH h : HS L N) : InfinitePlace L → Fin N → Fin N → ℂ)) (Pos L N) := by
      refine contDiffOn_pi' fun w => contDiffOn_pi' fun a => contDiffOn_pi' fun b => ?_
      intro h hh
      have hdet : (mat h w).det ≠ 0 := ((hh w).det_pos).ne'
      exact (cd_inv (fun h : HS L N => mat h w) (fun i j => hent w i j) b a h hdet).contDiffWithinAt
    have e : (dualH : HS L N → HS L N) =
        fun h => P ((dualH h : HS L N) : InfinitePlace L → Fin N → Fin N → ℂ) := by
      funext h; exact (hP (dualH h)).symm
    rw [e]
    exact P.contDiff.comp_contDiffOn hF

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
end
