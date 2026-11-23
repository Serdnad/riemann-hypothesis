module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.CloudPropOfMapsRetractionBasis
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudDefs
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FactorizationBoundMonoLattices
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LatticeCountPrimeMonoLevel
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CcDualWtAnti
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.Bundle002
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle010
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle004
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.Bundle007
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.SubYGenCoefHom
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.Bundle003
public import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideDef
import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideFinal
public import Formalism.PeriodIntegrals.AdmissibleModel.WeylDim
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Tensor
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.GrowthOfBasic
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.MemInvariantSectionsIffIntegral
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
import Mathlib.Order.Interval.Finset.Box
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.BlockSubstitutionEmbedding

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems Formalism.GradedWeylDivisibility

section

variable {p n' : ℕ} {R : RS p n'} {m : ℕ}

theorem cc_elem (X : Fin n' → Fin (m + 1) → ℤ) (e : Edge R.W R.Qq (m + 1))
    (G : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf)
    (hs : (fun s : Fin n' => extO R.O R.ι R.σ s.val e.src) = famD R.O G 1)
    (hle : (fun s : Fin n' => LeAt p R.ι R.σ R.w s.val e) = famD R.O G (algebraMap R.O R.Kf R.w))
    (x : Vsp R.Kf X) (h1 : ((1 : R.Kf) ^ Ar 1 X) • x ∈ toV X (Hten R.O X (famD R.O G 1)))
    (hw : ((algebraMap R.O R.Kf R.w) ^ Ar 1 X) • x ∈ toV X (Hten R.O X (famD R.O G (algebraMap R.O R.Kf R.w)))) :
    x ∈ HL (O := R.O) R.ι R.σ X e.src ∧ x ∈ Re p R.ι R.σ R.w 1 X e := by
  constructor
  · show x ∈ toV X (Hten R.O X (fun s : Fin n' => extO R.O R.ι R.σ s.val e.src))
    rw [hs]
    rwa [one_zpow, one_smul] at h1
  · refine (cc_mem_scale (zpow_ne_zero _ R.w_ne)).2 ?_
    rw [zpow_neg, inv_inv]
    show _ ∈ toV X (Hten R.O X (fun s : Fin n' => LeAt p R.ι R.σ R.w s.val e))
    rw [hle]
    exact hw

end

theorem restCloudMaps_of (h : RestCloudLat) (hIncl : DualHeightInclusion) : RestCloudMaps := by
  classical
  intro p n' R mm hmm TT a ccl aw bw lam0 A B hBase hDom hzero hAB h8 e he
  obtain ⟨mH, mU, abelian₂, hint, hel⟩ :=
    h p n' R mm hmm TT a ccl aw bw lam0 A B hBase hDom hzero hAB h8 _ _ _ _ _ rfl rfl rfl rfl rfl
  obtain ⟨G, hG, hs, hle, ht⟩ := cc_edge R e he
  obtain ⟨nb, z0, s, s', ka, hnb, hka, h24, hmem⟩ := hel G hG
  have hw : algebraMap R.O R.Kf R.w ≠ 0 := R.w_ne
  have hIH : IntB R mH := fun M hM => (hint M hM).1
  have hIU : IntB R mU := fun M hM => (hint M hM).2.1
  have hIL : IntB R abelian₂ := fun M hM => (hint M hM).2.2

  obtain ⟨hlo1, hlo2⟩ := cc_lo TT ccl aw bw lam0 A B hBase hzero hAB
  obtain ⟨hlo1', hlo2'⟩ := cc_dualW TT _ _ hlo1 hlo2
  have hze1 : ∀ s ∈ TT, flatW (mm + 1) (fun _ : TT => 2 * ccl) (fun _ : TT => 2 * ccl) s 0 = ((2 * ccl : ℕ) : ℤ) ∧
      flatW (mm + 1) (fun _ : TT => 2 * ccl) (fun _ : TT => 2 * ccl) s (Fin.last (mm + 1)) = -((2 * ccl : ℕ) : ℤ) :=
    fun s hs => ⟨cc_flat_zero _ _ _ s hs, cc_flat_last _ _ _ s hs⟩
  obtain ⟨aze, -⟩ := cc_Ar_of TT _ _ hze1 (fun s hs => cc_flat_off _ _ _ s hs)
  obtain ⟨alo, -⟩ := cc_Ar_of TT _ _ hlo1 hlo2
  obtain ⟨alo', elo'⟩ := cc_Ar_of TT _ _ hlo1' hlo2'
  have aHp : Ar 1 (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl)) =
      Ar 1 (flatW (mm + 1) A B) + Ar 1 (flatW (mm + 1) (fun _ : TT => 2 * ccl) (fun _ : TT => 2 * ccl)) := by
    rw [← cc_Ar_add, ← cc_flat_add]
  have alam : Ar 1 lam0 = Ar 1 (flatW (mm + 1) A B) + Ar 1 (lam0 - flatW (mm + 1) A B) := by
    rw [← cc_Ar_add, add_sub_cancel]
  have aL : Ar 1 (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl)) =
      Ar 1 lam0 + Ar 1 (dualW (lam0 - flatW (mm + 1) A B)) := by
    rw [aHp, alam, aze, alo, alo']
    push_cast
    ring
  have hdlo : IsDominant (lam0 - flatW (mm + 1) A B) := cc_lo_dom TT ccl aw bw lam0 A B hBase hDom hzero hAB
  have hdlo' : IsDominant (dualW (lam0 - flatW (mm + 1) A B)) := fun s => cc_dualWt_anti _ (hdlo s)

  obtain ⟨z1, sb1, sa1, -⟩ := hmem 1 one_ne_zero
  obtain ⟨zw, sbw, saw, isow⟩ := hmem _ hw
  obtain ⟨-, -, sap, -⟩ := hmem _ (mul_ne_zero hw hw)
  obtain ⟨hz1, hz2⟩ := cc_elem _ e G hs hle z0 z1 zw
  refine ⟨nb, mH.flip z0, fun b => mU.flip (s b), fun a' => abelian₂.flip (s' a'), ka, hnb, hka, ?_, ?_, ?_⟩
  · intro a' b F
    exact h24 a' b F
  · intro F
    constructor
    · intro hF
      have h1 := (cc_mem_scale (zpow_ne_zero _ hw)).1 hF
      rw [zpow_neg, inv_inv] at h1
      have h2 : mH ((algebraMap R.O R.Kf R.w ^ Ar 1 (flatW (mm + 1) A B)) • F)
          ((algebraMap R.O R.Kf R.w ^ Ar 1 (flatW (mm + 1) (fun _ : TT => 2 * ccl) (fun _ : TT => 2 * ccl))) • z0) =
          (algebraMap R.O R.Kf R.w ^ Ar 1 (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl))) •
            mH.flip z0 F := by
        rw [map_smul, map_smul, LinearMap.smul_apply, smul_smul, ← zpow_add₀ hw, aHp, LinearMap.flip_apply,
          add_comm (Ar 1 (flatW (mm + 1) A B))]
      have h3 := isow ((algebraMap R.O R.Kf R.w ^ Ar 1 (flatW (mm + 1) A B)) • F) (by
        rw [h2, ← hle]
        exact h1)
      refine (cc_mem_scale (zpow_ne_zero _ hw)).2 ?_
      rw [zpow_neg, inv_inv]
      show _ ∈ toV _ (Hten R.O _ (fun s : Fin n' => LeAt p R.ι R.σ R.w s.val e))
      rw [hle]
      exact h3
    · intro hF
      exact cc_Re hIH aHp e he F hF z0 hz2
  · intro t c₂ hc
    refine ⟨?_, ?_, ?_⟩
    · intro F hF
      exact cc_CCL hIncl hIH aHp (flattened_weight_dominant _ _ _) e he z0 hz1 hz2 t c₂ F hF
    · intro b F hF
      obtain ⟨hb1, hb2⟩ := cc_elem _ e G hs hle (s b) (sb1 b) (sbw b)
      exact cc_CCL hIncl hIU alam hdlo e he (s b) hb1 hb2 t c₂ F hF
    · intro a' g hg
      obtain ⟨-, ha2⟩ := cc_elem _ e G hs hle (s' a') (sa1 a') (saw a')
      have ha3 : ((algebraMap R.O R.Kf R.w * algebraMap R.O R.Kf R.w) ^ Ar 1 (dualW (lam0 - flatW (mm + 1) A B))) • s' a' ∈
          HL (O := R.O) R.ι R.σ (dualW (lam0 - flatW (mm + 1) A B)) e.tgt := by
        show _ ∈ toV _ (Hten R.O _ (fun s : Fin n' => extO R.O R.ι R.σ s.val e.tgt))
        rw [ht]
        exact sap a'
      have h5 := cc_CCL' hIL aL hdlo' (by rw [elo', alo']) (TT.card * ccl) (by rw [alo']; push_cast; ring) e he (s' a')
        ha3 ha2 t c₂ (by rw [← mul_assoc]; exact hc) g hg
      rw [← mul_assoc] at h5
      exact h5

end Formalism.MainNotions.flipOneThree.Pf

end
end

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.flipOneThree.Pf.QB

theorem lamMemP : LamMemP := by
  intro K _ _ r N ν ν' νp L hνl hν'l hνpl hνp0 hνpm hPh v hv t ht
  have hsv := fun u => subCoeffP K r ν v hv u
  have hst := fun u => subCoeffP K r ν' t ht u
  obtain ⟨hvw, hvi⟩ := mem_dualWeyl_iff.mp hv
  obtain ⟨htw, hti⟩ := mem_dualWeyl_iff.mp ht
  set F := lamOf K r L (blockEmb K true v * blockEmb K false t) with hF
  have hscale : ∀ t0 : Fin (r + 1 + 1), ∀ c : K, c ≠ 0 →
      scCol K (r + 1 + 1) t0 c F = c ^ νp t0 • F := by
    intro t0 c hc
    rcases midOf_cases t0 with ⟨j, rfl⟩ | ⟨hn, h0 | hl⟩
    · rw [hνpm j]
      exact lam_scaleM L N _ _ hPh j c hc v t hsv hst
    · rw [lam_scaleN L t0 hn c ν ν' v t hvw htw]
      subst h0
      rw [hνp0]
    · rw [lam_scaleN L t0 hn c ν ν' v t hvw htw]
      subst hl
      rw [hνl, hν'l, hνpl]
  have hcol : ∀ (l j : Fin (r + 1 + 1)), l < j → ∀ c : K, colAdd K l j c F = F := by
    intro l j hlj c
    rcases midOf_cases j with ⟨j', rfl⟩ | ⟨hn, h0 | hl⟩
    · rcases midOf_cases l with ⟨l', rfl⟩ | ⟨hn', h0' | hl'⟩
      · have hne : l' ≠ j' := by
          rintro rfl
          exact lt_irrefl _ hlj
        exact lam_addM L N _ _ hPh l' j' hne c v t hsv hst
      · subst h0'
        exact lam_addC L j' c v t hvi hti
      · subst hl'
        exact absurd hlj (not_lt.mpr (Fin.le_last _))
    · subst h0
      exact absurd hlj (Fin.not_lt_zero _)
    · subst hl
      apply colAdd_trivial
      intro m hm
      rw [wt_of_scale (Fin.last (r + 1)) (νp (Fin.last (r + 1))) F (hscale _) m hm, hνpl]
  rw [mem_dualWeyl_iff]
  refine ⟨?_, ?_⟩
  · intro m hm
    funext t0
    exact wt_of_scale t0 (νp t0) F (hscale t0) m hm
  · intro l j hlj
    apply MvPolynomial.funext
    intro x
    have h1 := congrArg (fun φ => φ F) (lsat_eval_colAddGen (R := K) l j x)
    simp only [AlgHom.comp_apply, hcol l j hlj] at h1
    simpa [MvPolynomial.eval_rename, MvPolynomial.coe_aeval_eq_eval] using h1

theorem subCoeffP : SubCoeffP := QB.subCoeffP

end Formalism.MainNotions.flipOneThree.Pf

end
end

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem pb_nabla_one {O K : Type} [CommRing O] [Field K] [Algebra O K] (m : ℕ) (lam : Fin (m + 1) → ℤ) :
    nablaLTw O K m lam 1 = intO O (m + 1) (nuOf lam) := by
  ext F
  rw [Formalism.GradedWeylDivisibility.nablaLTwMem O K m lam 1 (by simp) F, Matrix.det_one, one_zpow, one_smul, tn_rowAct_one]
  exact Iff.rfl

theorem pb_finrank (K : Type) [Field K] (n : ℕ) (nu : Fin n → ℕ) (hnu : Antitone nu) :
    (Module.finrank K (dualWeyl K n n nu) : ℚ) = weylDim n (fun i => (nu i : ℤ)) := by
  rw [Formalism.L2.G.Model.weyl_dualWeyl K n nu hnu]
  unfold weylDim
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  push_cast
  rfl

theorem pb_smith_lam {p n' : ℕ} (R : RS p n') (m : ℕ) (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) :
    ∃ B : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf] MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf] R.Kf,
      (∀ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf) (P Q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf),
        B (rowAct R.Kf g P) Q = B P (rowAct R.Kf g.transpose Q)) ∧
      (∀ P ∈ intO R.O (m + 1) (nuOf lam), ∀ Q ∈ intO R.O (m + 1) (nuOf lam), B P Q ∈ Set.range (algebraMap R.O R.Kf)) ∧
      ∃ (nb : ℕ) (x x' : Fin nb → MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) (ka : Fin nb → ℕ),
        (nb : ℚ) = weylDim (m + 1) (fun j => (nuOf lam j : ℤ)) ∧ (∀ b, ka b ≤ Formalism.L2.G.Model.expN p m lam) ∧
        (∀ b, x b ∈ intO R.O (m + 1) (nuOf lam)) ∧ (∀ a', x' a' ∈ intO R.O (m + 1) (nuOf lam)) ∧
        ∀ a' b, B (x b) (x' a') = if a' = b then (p : R.Kf) ^ ka b else 0 := by
  classical
  have hfr := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  obtain ⟨B0, ha, hb, hc, hd⟩ :=
    Formalism.L2.G.Model.formCore p n' R.W R.Qq R.O R.Kf R.ι R.σ R.jO R.w R.std.1 m lam hlam
  obtain ⟨Bs, -, hB1, hB3, hB2⟩ := la_basis hinj m lam 1 (by rw [Matrix.det_one]; exact isUnit_one)
  rw [pb_nabla_one] at hB1
  have : Fintype ↥(ssIdx (m + 1) (m + 1) (nuOf lam)) := (sSIdxFinite _ _ _).fintype
  let e : Fin (Fintype.card ↥(ssIdx (m + 1) (m + 1) (nuOf lam))) ≃ ↥(ssIdx (m + 1) (m + 1) (nuOf lam)) :=
    (Fintype.equivFin _).symm
  have hrange : Set.range (Bs ∘ e) = Set.range Bs := e.surjective.range_comp Bs
  have hli : LinearIndependent R.Kf (Bs ∘ e) := hB3.comp e e.injective
  have hsK : Submodule.span R.Kf (Set.range (Bs ∘ e)) = dualWeyl R.Kf (m + 1) (m + 1) (nuOf lam) := by rw [hrange, hB2]
  have hsO : Submodule.span R.O (Set.range (Bs ∘ e)) = intO R.O (m + 1) (nuOf lam) := by rw [hrange, hB1]
  have hpc : algebraMap R.O R.Kf (p : R.O) = (p : R.Kf) := map_natCast _ p
  obtain ⟨x, x', ka, hka, hx, hx', hdiag⟩ := pb_abs (O := R.O) (K := R.Kf) R.w (p : R.O) R.std.2.1 R.std.1.w_sq
    (Formalism.L2.G.Model.expN p m lam) _ (Bs ∘ e) hli B0
    (by rw [hsK]; exact hb)
    (by rw [hsK, hsO]; exact hc)
    (by rw [hsO, hpc]; exact hd)
  rw [hsO] at hx hx'
  rw [hpc] at hdiag
  refine ⟨((p : R.Kf) ^ Formalism.L2.G.Model.expN p m lam) • B0, ?_, ?_, _, x, x', ka, ?_, hka, hx, hx', ?_⟩
  · intro g P Q
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, ha]
  · intro P hP Q hQ
    have h := hd Q hQ P hP
    rw [map_smul] at h
    rw [LinearMap.smul_apply, LinearMap.smul_apply]
    exact h
  · rw [← pb_finrank R.Kf (m + 1) (nuOf lam) (nuOf_anti lam hlam), ← hsK, finrank_span_eq_card hli, Fintype.card_fin]
  · intro a' b
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
    exact hdiag a' b

theorem smithP : SmithP := by
  intro p n' R m ν hνA hν0
  have hlam : Antitone (fun j => ((ν j : ℕ) : ℤ)) := fun i j h => by
    show ((ν j : ℕ) : ℤ) ≤ ((ν i : ℕ) : ℤ)
    exact_mod_cast hνA h
  have hnu : nuOf (fun j => ((ν j : ℕ) : ℤ)) = ν := by
    funext t
    simp only [nuOf, hν0]
    simp
  have hexp : Formalism.L2.G.Model.expN p m (fun j => ((ν j : ℕ) : ℤ)) ≤ N0 (m + 1) * deF p (m + 1) (ν 0) := by
    unfold Formalism.L2.G.Model.expN
    split_ifs
    · exact Nat.zero_le _
    · have : ellWt (fun j : Fin (m + 1) => ((ν j : ℕ) : ℤ)) = ν 0 := by
        unfold ellWt
        have hl : lastIdx (m + 1) = Fin.last m := Fin.ext (by simp [lastIdx])
        rw [hl]
        show (((ν 0 : ℕ) : ℤ) - ((ν (Fin.last m) : ℕ) : ℤ)).toNat = ν 0
        rw [hν0]
        simp
      rw [this]
  obtain ⟨B, h1, h2, nb, x, x', ka, h3, h4, h5, h6, h7⟩ := pb_smith_lam R m _ hlam
  rw [hnu] at h2 h3 h5 h6
  exact ⟨B, h1, h2, nb, x, x', ka, h3, fun b => (h4 b).trans hexp, h5, h6, h7⟩

end Formalism.MainNotions.flipOneThree.Pf

end
end
