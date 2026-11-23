module

public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.Bundle007
import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.RestrictedWeightFirstTwoEq
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.TestSideCounting
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.Bundle003
import Formalism.LocalToGlobal.GroupLattices.FockModels.ElementaryDivisorBasis
import Formalism.LocalToGlobal.GroupLattices.FockModels.FlatModels.EdgeLatOfG
import Formalism.LocalToGlobal.GroupLattices.FockModels.FlatModels.LetterWtAnti
public import Formalism.PeriodIntegrals.AdmissibleModel.WeylDim
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.Bundle004
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.Bundle001
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.Bundle005
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial
open Formalism.L2.G.Model (Nv)


set_option maxHeartbeats 1600000 in
theorem primStep_of (hTr : TransStep) (hSub : SubstPol) (C CLa : ℝ) (hSP : SPStep C) : PrimStep C CLa := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K
    _ _ hk hrk F hF E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis
  let _ : Algebra (WF p n') O := algOfIdent j φ
  intro FsB hFsB Θ hΘ
  have hkr : orbitWindowCount r de h x + 2 * r ≤ (m + 1) - r := H.2.2.2.2.2.2.2.1
  have hr2 : 2 ≤ r := H.2.1
  have hm2 : 2 ≤ m := by omega
  have hdom : IsDominant lam0 := H.2.2.2.2.1.2.1
  have hwirr : Irreducible w := hSet.2.1
  set ν : Fin n' → Fin (m + 1) → ℕ := fun s => nuOf (lamAt (restW TT lam0) s) with hν
  set top : Fin n' → Bool := fun s => decide (s ∈ TT) with htop
  let I := ∀ s : Fin n', Xs m (top s) (vecE n' s) (ν s)
  have : Finite I := Pi.finite
  let _ : Fintype I := Fintype.ofFinite I
  let eI : I ≃ Fin (Nat.card I) := Finite.equivFin I
  have hbas := fun s => sSBasis O (m + 1) (m + 1) (ν s)
  choose b hb1 hb2 using hbas
  let bX : ∀ s, Xs m (top s) (vecE n' s) (ν s) → MvPolynomial (Fin (m + 1) × Fin (m + 1)) O :=
    fun s y => b s ⟨y.1, y.2.1⟩
  let sO : I → MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) O := fun i => ∏ s, blockEmb O s (bX s (i s))
  have hsO : ∀ i, sO i ∈ tensorLat O O (fun s => dualWeyl O (m + 1) (m + 1) (nuOf (lamAt (restW TT lam0) s))) := by
    intro i
    refine Submodule.subset_span ⟨fun s => bX s (i s), fun s => ?_, rfl⟩
    show bX s (i s) ∈ dualWeyl O (m + 1) (m + 1) (ν s)
    rw [← (hb1 s).2.1]
    exact Submodule.subset_span ⟨_, rfl⟩
  obtain ⟨sh', hsh, hmain⟩ := hTr p n' W Qq O Kf ι σ j w hSet.1 φ hφ m r hm2 (by omega) (by omega) (dT TT lam0)
    (restW TT lam0) lam0 (lambda_zero_eq_product TT lam0) (restW_dom (by omega) TT lam0 hdom) e he hm g hhm hg hbasis Θ hΘ I sO hsO
  refine ⟨Nat.card I, fun i => sh' (eI.symm i), fun i => hsh _, card_all hm2 TT lam0 hdom, ?_⟩
  intro S hS c hcu hmem
  obtain ⟨x0, hx0⟩ := hcu
  obtain ⟨SPO, hSPO1, hSPO2⟩ := hSP p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ
    hrk F hF g hg (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x)
  let P : I → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) :=
    fun i => ∑ bb, c (bb, eI i) • FsB bb
  let T0 : I → RRing O n' (r + K) := fun i => ∑ bb, c (bb, eI i) • B bb
  let Q : I → MvPolynomial (Fin n' × Fin (m + 1)) O := fun i => rename (castV hk) (T0 i) * SPO
  have hPQ : ∀ i, subst p n' O w n' r g (P i : MvPolynomial (TV n' (m + 1)) (KK O)) =
      map (algebraMap O (KK O)) (Q i) := by
    intro i
    have e1 : ((P i : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O)) :
        MvPolynomial (TV n' (m + 1)) (KK O)) =
        ∑ bb, algebraMap O (KK O) (c (bb, eI i)) • (FsB bb : MvPolynomial (TV n' (m + 1)) (KK O)) := by
      simp only [P, Submodule.coe_sum, Submodule.coe_smul, algebraMap_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_smul, hFsB, symB, toK, Q, T0, map_mul, map_sum, ← hSPO1, Finset.sum_mul]
    refine Finset.sum_congr rfl fun bb _ => ?_
    simp only [MvPolynomial.smul_eq_C_mul, map_mul, map_C, mul_assoc]
  have hv : (((∑ y, c y • S y : Vsp Kf lam0)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
      ∑ i, ((Θ (P i) : Vsp Kf (flW (m := m) (dT TT lam0))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) *
        ((sh' i : Vsp Kf (restW TT lam0)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) := by
    have e2 : ∀ i, ((Θ (P i) : Vsp Kf (flW (m := m) (dT TT lam0))) :
        MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
        ∑ bb, c (bb, eI i) • ((Θ (FsB bb) : Vsp Kf (flW (m := m) (dT TT lam0))) :
          MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) := by
      intro i
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [P, map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul_of_tower]
    simp only [e2, Submodule.coe_sum, Submodule.coe_smul_of_tower, Finset.sum_mul]
    rw [Fintype.sum_prod_type, Finset.sum_comm, ← Equiv.sum_comp eI]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun bb _ => ?_
    rw [hS bb (eI i)]
    simp only [Equiv.symm_apply_apply, smul_mul_assoc]
  obtain ⟨R, hR⟩ := hmain P Q hPQ _ hv hmem

  let Fr := IsLocalRing.ResidueField O
  let res : O →+* Fr := IsLocalRing.residue O
  have hresw : res w = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hwirr.not_isUnit
  have h0 : ∑ i ∈ (Finset.univ : Finset I), thAll Fr n' m (vecE n') (map res (Q i)) *
      ∏ s, blockEmb Fr s (map res (bX s (i s))) = 0 := by
    have h1 := congrArg (map res) hR
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_thAll, map_C, hresw, C_0, zero_mul, sO, map_prod, blockEmb, map_rename] at h1
    simpa only [blockEmb] using h1
  have hQhom : ∀ i, IsMultiHom (dT TT lam0) (map res (Q i)) := by
    intro i ee hee s
    have h1 : ee ∈ (Q i).support := support_map_subset res (Q i) hee
    have h2 : ee ∈ (map (algebraMap O (KK O)) (Q i)).support := by
      rw [support_map_of_injective _ (IsFractionRing.injective O (KK O))]
      exact h1
    rw [← hPQ i] at h2
    have h3 := hSub p n' W Qq O Kf ι σ j w hSet.1 φ hφ (m + 1) r (dT TT lam0) g hg _ (P i).2
    exact (Formalism.L2.G.Model.mem_Pol.1 h3) ee h2 s
  have hQ0 := bigInd Fr n' m hm2 top (vecE n') (dT TT lam0) ν
    (fun s hs => by
      have : s ∉ TT := by simpa [htop] using hs
      simp [dT, this])
    (fun s hs hv t ht => nu_odd (by omega) TT lam0 hdom s (by simpa [htop] using hs) hv t ht)
    (fun s y => map res (bX s y))
    (fun s y => by
      obtain ⟨d1, d2, -⟩ := hb2 s ⟨y.1, y.2.1⟩
      have := deg_map (colLex (m + 1) (m + 1)) res (bX s y) d2
      exact ⟨this.1.trans d1, this.2⟩)
    Finset.univ (fun i => map res (Q i)) hQhom h0
  have hq := hQ0 (eI.symm x0.2) (Finset.mem_univ _)
  simp only [Q, map_mul] at hq
  have hT : map res (rename (castV hk) (T0 (eI.symm x0.2))) = 0 := by
    rcases mul_eq_zero.1 hq with h1 | h1
    · exact h1
    · exact absurd h1 hSPO2
  rw [map_rename] at hT
  have hinj : Function.Injective (castV (n' := n') hk) := by
    intro u v huv
    simp only [castV, Prod.mk.injEq] at huv
    exact Prod.ext huv.1 (Fin.cast_injective _ huv.2)
  have hT' : map res (T0 (eI.symm x0.2)) = 0 := by
    apply rename_injective _ hinj
    rw [hT, map_zero]
  have hdvd : MvPolynomial.C w ∣ T0 (eI.symm x0.2) := by
    rw [C_dvd_iff_dvd_coeff]
    intro ee
    have h1 : res (AddMonoidAlgebra.coeff (T0 (eI.symm x0.2)) ee) = 0 := by
      simp only [← coeff_map, hT', AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    rw [IsLocalRing.residue_eq_zero_iff, hwirr.maximalIdeal_eq, Ideal.mem_span_singleton] at h1
    exact h1
  obtain ⟨y, hy⟩ := hdvd
  obtain ⟨T, hTc⟩ := hc
  have hfin := dvd_of_compl B hli T hTc w (fun bb => c (bb, x0.2)) y (by
    have : T0 (eI.symm x0.2) = ∑ bb, c (bb, x0.2) • B bb := by
      simp only [T0, Equiv.apply_symm_apply]
    rw [← this, hy, MvPolynomial.smul_eq_C_mul]) x0.1
  exact hwirr.not_isUnit (isUnit_of_dvd_unit hfin hx0)

theorem source_integrality_of_substitution (hTr : TransStep) (hSub : SubstPol) (C₀ : ℝ) (hC0 : 0 < C₀) (hSP : ∀ C, C₀ ≤ C → SPStep C)
    (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : SourcePrimitiveIntegrality D CLa Ck Crk Cdeg :=
  fun _ => ⟨C₀, hC0, fun C hC => primStep_of hTr hSub C CLa (hSP C hC)⟩

end Formalism.MainNotions.TestSideCounting
end
end

section

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial
open Formalism.L2.G.Model
open Formalism.MainNotions.G.LatticeSystems (la_tw lb_D la_tw_det lb_D_det H0_eq_twisted_nabla la_indep)

section

variable {p n' : ℕ} [Fact p.Prime] {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

theorem tr_theta (hS : HidaSetting p n' W Qq O Kf ι σ j w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ) (m r : ℕ)
    (hm : 1 ≤ m) (d : Fin n' → ℕ) (hmat : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hh : IsUnit hmat.det)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) (hg : IsGLW g)
    (P : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) (hP : P ∈ Pol (KK O) (m + 1) d)
    (Q : MvPolynomial (Fin n' × Fin (m + 1)) O) :
    letI : Algebra (WF p n') O := algOfIdent j φ
    subst p n' O w n' r g P = map (algebraMap O (KK O)) Q →
    (algebraMap O Kf w ^ (Avec (vecE n') d)) •
      ((∏ s, (Mx ι σ w φ r (fun x : Fin n' => x) hmat g s).det ^ (letterWt m (d s) (vecE n' s) (Fin.last m))) •
        blockAct Kf (Mx ι σ w φ r (fun x : Fin n' => x) hmat g)
          (thF hS m (vecE n') (fun x => la_tw ι σ x.val hmat) P)) =
      map (algebraMap O Kf) (Th0 O m (vecE n') Q) := by
  letI : Algebra (WF p n') O := algOfIdent j φ
  intro hPQ
  have hw := w_ne hS
  set c := algebraMap O Kf w with hc
  have hP' := (pol_iff hS _ _ _).1 hP
  have hM := Mx_det (ι := ι) (σ := σ) hw φ r (fun x : Fin n' => x) hmat hh g hg
  unfold thF
  rw [tr_multi_twist Kf m hm (vecE n') d _ hM _ (Lin_Pol _ _ hP'), Lin_comp]
  have h1 := lift_eq hS φ hφ r (LLT n') (fun x : Fin n' => x) (fun _ => rfl) g hg P
  have hB : Bm ι σ w φ r (LLT n').vec (fun x : Fin n' => x) g = fun x => (if (LLT n').vec x then c else 1) •
      (Aa ((LLT n').vec x) (la_tw ι σ x.val hmat)⁻¹ *
        Aa ((LLT n').vec x) (Mx ι σ w φ r (fun x : Fin n' => x) hmat g x)) :=
    funext fun x => Bm_eq hw φ r (LLT n').vec (fun x : Fin n' => x) hmat hh g hg x
  rw [hB, Lin_smul _ _ _ hP'] at h1
  have hprod : ∏ x, (if (LLT n').vec x then c else 1) ^ d x = c ^ Avec (vecE n') d := by
    unfold Avec
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_congr rfl
    intro x _
    show (if vecE n' x then c else 1) ^ d x = _
    split_ifs <;> simp
  rw [hprod] at h1
  have h2 : map (kapR hS) (liftSubst p n' O w r (LLT n') g P) = map (algebraMap O Kf) Q := by
    have : liftSubst p n' O w r (LLT n') g P = map (algebraMap O (KK O)) Q := hPQ
    rw [this, map_map]
    have hk : (kapR hS).comp (algebraMap O (KK O)) = algebraMap O Kf := RingHom.ext fun x => kapR_alg hS x
    rw [hk]
  rw [map_letter_substitution, ← h2, h1, map_smul]
  rfl

end

theorem transStep : TransStep := by
  intro p n' _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS φ hφ m r hm hr1 hr2 d rest lam0 hlam hrest e he hmat g hh hg hbasis
  letI : Algebra (WF p n') O := algOfIdent j φ
  intro Θ hΘ I _ sO hsO
  have hfrac := hS.frac_O
  have hinj : Function.Injective (algebraMap O Kf) := IsFractionRing.injective O Kf
  have hw := w_ne hS
  set c := algebraMap O Kf w with hc
  set M : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf := Mx ι σ w φ r (fun x : Fin n' => x) hmat g with hMdef
  have hM : ∀ s, IsUnit (M s).det := Mx_det hw φ r _ hmat hh g hg
  have hH : ∀ lam : Fin n' → Fin (m + 1) → ℤ, IsDominant lam →
      Hten O lam (fun s => LeAt p ι σ w s.val e) = tensorLat O Kf (fun s => nablaLTw O Kf m (lamAt lam s) (M s)) := by
    intro lam hl
    unfold Hten
    congr 1
    funext s
    show H0 O m _ (LeAt p ι σ w s.val e) = _
    rw [(edgeLat_of hS m r e _ hbasis).2.1]
    show H0 O m _ (colSpan O (M s)) = _
    rw [H0_eq_twisted_nabla (la_indep hinj) _ _ (lamAt_antitone' lam hl s) _ (hM s)]
  have hV : ∀ lam : Fin n' → Fin (m + 1) → ℤ, IsDominant lam →
      Vsp Kf lam = tensorLat Kf Kf (fun s => dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam s))) := by
    intro lam hl
    unfold Vsp
    congr 1
    funext s
    rw [if_pos (lamAt_antitone' lam hl s)]
  have hfl : IsDominant (flW (m := m) d) := flW_dom d
  have hl0 : IsDominant lam0 := by rw [hlam]; exact isDominant_add hfl hrest
  let dt : (Fin n' → Fin (m + 1) → ℤ) → Kf := fun lam => ∏ s, (M s).det ^ (lamAt lam s (Fin.last m))
  have hdt : dt lam0 = dt (flW d) * dt rest := by
    show ∏ s, _ = (∏ s, _) * ∏ s, _
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [hlam, lamAt_add, Pi.add_apply, zpow_add₀ (hM s).ne_zero]
  have hAr : Ar r lam0 = Ar r (flW (m := m) d) + Ar r rest := by rw [hlam, Ar_add]
  have h1 := fun i => tr_tens_lift O Kf m (fun s => lamAt rest s) M hM (sO i) (hsO i)
  choose y hy1 hy2 using h1
  have hyV : ∀ i, y i ∈ Vsp Kf rest := by
    intro i
    rw [hV rest hrest]
    exact tr_tens_le O Kf m _ M hM _ (hy1 i)
  refine ⟨fun i => c ^ (-Ar r rest) • (⟨y i, hyV i⟩ : Vsp Kf rest), ?_, ?_⟩
  · intro i
    refine ⟨⟨y i, hyV i⟩, ?_, rfl⟩
    show y i ∈ Hten O rest (fun s => LeAt p ι σ w s.val e)
    rw [hH rest hrest]
    exact hy1 i
  · intro P Q hPQ v hv hvmem
    obtain ⟨y0, hy0, hvy⟩ := (mem_scale2 (O := O) (Vsp Kf lam0) (Hten O lam0 fun s => LeAt p ι σ w s.val e)
      (c ^ (1 : ℤ)) (c ^ (-Ar r lam0)) (zpow_ne_zero _ hw) (zpow_ne_zero _ hw) v).1 hvmem
    rw [hH lam0 hl0] at hy0
    obtain ⟨R0, hR0⟩ := tr_tens_int O Kf m (fun s => lamAt lam0 s) M hM y0 hy0
    refine ⟨R0, ?_⟩
    apply map_injective _ hinj
    have way1 : (c ^ (Ar r lam0) * dt lam0) • blockAct Kf M (v : MvPolynomial _ Kf) =
        map (algebraMap O Kf) (C w * R0) := by
      rw [hvy, map_smul, smul_smul, map_mul, map_C, ← hR0, ← smul_eq_C_mul, smul_smul]
      congr 1
      have hcc : c ^ Ar r lam0 * c ^ (-Ar r lam0) = 1 := by rw [← zpow_add₀ hw, add_neg_cancel, zpow_zero]
      show c ^ Ar r lam0 * dt lam0 * (c ^ (1 : ℤ) * c ^ (-Ar r lam0)) = c * dt lam0
      rw [zpow_one]
      linear_combination (dt lam0 * c) * hcc
    have hA : Ar r (flW (m := m) d) = (Avec (vecE n') d : ℤ) :=
      flat_Ar r hr1 hr2 (vecE n') d (flW d) (isFlat_flW d)
    have hdfl : dt (flW d) = ∏ s, (M s).det ^ (letterWt m (d s) (vecE n' s) (Fin.last m)) := by
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [flat_lam (vecE n') d (flW d) (isFlat_flW d) s]
    have way2 : (c ^ (Ar r lam0) * dt lam0) • blockAct Kf M (v : MvPolynomial _ Kf) =
        map (algebraMap O Kf) (∑ i, thAll O n' m (vecE n') (Q i) * sO i) := by

      rw [hv, map_sum, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have t1 := tr_theta hS φ hφ m r (by omega) d hmat hh g hg (P i).1 (P i).2 (Q i) (hPQ i)
      rw [map_mul, map_mul, ← hy2 i]
      have e1 : map (algebraMap O Kf) (thAll O n' m (vecE n') (Q i)) = map (algebraMap O Kf) (Th0 O m (vecE n') (Q i)) :=
        rfl
      rw [e1, ← t1, hΘ (P i), hAr, hdt, hdfl, hA, zpow_add₀ hw, zpow_natCast]
      show _ • (_ * blockAct Kf M (c ^ (-Ar r rest) • y i)) = _
      rw [map_smul]
      simp only [smul_eq_C_mul, map_mul, map_pow]
      have hcc : (C (c ^ Ar r rest) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * C (c ^ (-Ar r rest)) = 1 := by
        rw [← C_mul, ← zpow_add₀ hw, add_neg_cancel, zpow_zero, C_1]
      linear_combination (C c ^ Avec (vecE n') d * C (∏ s, (M s).det ^ (letterWt m (d s) (vecE n' s) (Fin.last m))) *
        C (dt rest) * blockAct Kf M (thF hS m (vecE n') (fun x => la_tw ι σ x.val hmat) (P i).1) *
        blockAct Kf M (y i)) * hcc
    rw [← way2, way1]

end Formalism.MainNotions.TestSideCounting
end
end
