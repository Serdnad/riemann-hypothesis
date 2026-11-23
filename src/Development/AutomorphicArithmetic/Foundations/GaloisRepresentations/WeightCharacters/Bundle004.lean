module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1742
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle296
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching

namespace UpperTheory.Gal.Wt

private theorem pev_map {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ}
    (P' : MvPolynomial (Fin a × Fin a) (Qbar l)) (h : GL (Fin a) ℂ) :
    ι.symm (pev (MvPolynomial.map ι.toRingHom P') h) =
      MvPolynomial.eval (fun p : Fin a × Fin a => ι.symm ((h : Matrix (Fin a) (Fin a) ℂ) p.1 p.2)) P' := by
  induction P' using MvPolynomial.induction_on with
  | C c => simp [pev]
  | add p q hp hq =>
    simp only [pev, map_add (f := _)] at hp hq ⊢
    rw [hp, hq]
  | mul_X p i hp =>
    simp only [pev, map_mul, MvPolynomial.map_X, MvPolynomial.eval_X] at hp ⊢
    rw [hp]

theorem pieces_of (hS : SepPoly) (hN : NearSub) : Pieces := by
  intro l _ ι a Γ _ _ _ _ φ hcont hint Γ' hΓ' hker ε hε
  obtain ⟨H, hHo, hH⟩ := hN l ι a Γ φ hcont hint ε hε
  set K : Subgroup Γ := H ⊓ Γ' with hK
  have hKo : IsOpen (K : Set Γ) := by
    rw [hK, Subgroup.coe_inf]
    exact hHo.inter hΓ'
  have hkerK : φ.ker ≤ K := by
    intro g hg
    refine Subgroup.mem_inf.mpr ⟨(hH g).2 ?_, hker hg⟩
    intro i j
    rw [MonoidHom.mem_ker.mp hg]
    simpa using hε.le
  haveI : Finite (Γ ⧸ K) := Subgroup.quotient_finite_of_isOpen K hKo
  letI : Fintype (Γ ⧸ K) := Fintype.ofFinite _
  let c : Γ ⧸ K → Γ := fun q => q.out
  let v : Γ → (Fin a × Fin a → Qbar l) := fun g p => ι.symm ((φ g : Matrix (Fin a) (Fin a) ℂ) p.1 p.2)
  have hv : Continuous v := continuous_pi fun p => hcont p.1 p.2
  have hKc : IsClosed (K : Set Γ) := Subgroup.isClosed_of_isOpen K hKo
  have hinj : ∀ g g', v g = v g' → g⁻¹ * g' ∈ K := by
    intro g g' hgg
    apply hkerK
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
    apply Units.ext
    apply Matrix.ext
    intro i j
    exact ι.symm.injective (congrFun hgg (i, j))
  have hsep : ∀ q : Γ ⧸ K, ∃ P' : MvPolynomial (Fin a × Fin a) (Qbar l),
      (∀ z ∈ v '' {g | (c q)⁻¹ * g ∈ K}, ‖MvPolynomial.eval z P' - 1‖ ≤ ε) ∧
      (∀ z ∈ v '' {g | (c q)⁻¹ * g ∉ K}, ‖MvPolynomial.eval z P'‖ ≤ ε) := by
    intro q
    have hc1 : IsCompact (v '' {g | (c q)⁻¹ * g ∈ K}) :=
      (hKc.preimage (continuous_const.mul continuous_id)).isCompact.image hv
    have hc2 : IsCompact (v '' {g | (c q)⁻¹ * g ∉ K}) :=
      (hKo.isClosed_compl.preimage (continuous_const.mul continuous_id)).isCompact.image hv
    have hd : Disjoint (v '' {g | (c q)⁻¹ * g ∈ K}) (v '' {g | (c q)⁻¹ * g ∉ K}) := by
      rw [Set.disjoint_left]
      rintro z ⟨g, hg, rfl⟩ ⟨g', hg', hgg⟩
      apply hg'
      have hm := K.mul_mem hg (hinj g g' hgg.symm)
      simpa [mul_assoc] using hm
    exact hS (Qbar l) (Fin a × Fin a) _ _ hc1 hc2 hd ε hε
  choose P' hP1 hP2 using hsep
  refine ⟨Γ ⧸ K, inferInstance, c, fun q => MvPolynomial.map ι.toRingHom (P' q), ?_⟩
  intro g
  have hmem : ∀ q : Γ ⧸ K, (c q)⁻¹ * g ∈ K ↔ q = (g : Γ ⧸ K) := by
    intro q
    rw [← QuotientGroup.eq]
    simp [c]
  have h0 : (c (g : Γ ⧸ K))⁻¹ * g ∈ K := (hmem _).2 rfl
  refine ⟨(g : Γ ⧸ K), (Subgroup.mem_inf.mp h0).2, (hH _).1 (Subgroup.mem_inf.mp h0).1, ?_, ?_⟩
  · beta_reduce
    rw [map_sub, map_one, pev_map]
    exact hP1 _ _ ⟨g, h0, rfl⟩
  · intro q hq
    beta_reduce
    rw [pev_map]
    exact hP2 q _ ⟨g, fun h => hq ((hmem q).1 h), rfl⟩

end UpperTheory.Gal.Wt

end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.twist_of :
    UpperTheory.Gal.Wt.AutCrit → UpperTheory.Gal.Wt.Twist := by
  intro hA E _ _ _ a C hC ℓ hℓ W f c
  let e : UA E a → UA E a := fun g => (((ℓ g)⁻¹ * c : C) : UA E a)
  have he : ∀ g, e g ∈ finU (E := E) (n := a) := fun g => hC.fin ((ℓ g)⁻¹ * c).2
  let F : W.Sp →ₗ[ℂ] (UA E a → ℂ) :=
    { toFun := fun v g => f.1 v (g * e g)
      map_add' := fun v w => by funext g; simp
      map_smul' := fun r v => by funext g; simp }
  have hF : ∀ v g, F v g = f.1 v (g * e g) := fun _ _ => rfl
  have hleft : ∀ γ ∈ ratU E a, ∀ v g, F v (γ * g) = F v g := by
    intro γ hγ v g
    have h : e (γ * g) = e g := by simp only [e, hℓ.left γ hγ g]
    rw [hF, hF, h, mul_assoc]
    exact (f.2.1 v).left γ hγ _
  have hlev : ∀ k ∈ C, ∀ v g, F v (g * k) = F v g := by
    intro k hk v g
    have h : g * k * e (g * k) = g * e g := by
      simp only [e, hℓ.lev ⟨k, hk⟩ g, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hF, hF, h]
  have hinf : ∀ x ∈ infU E a, ∀ v g, F v (g * x) = f.1 v (g * x * e g) := by
    intro x hx v g
    have h : e (g * x) = e g := by simp only [e, hℓ.inf x hx g]
    rw [hF, h]
  have heqv : ∀ (x : infU E a) v, F (W.rep x v) = RU E a x (F v) := by
    intro x v
    funext g
    rw [RU_apply, hinf x x.2, hF, f.2.2 x v, RU_apply, mul_assoc g, mul_assoc g, fin_mul_inf (he g) x.2]
  have haut : ∀ v, IsAutFormU (F v) := by
    intro v
    refine hA E a C hC (F v) (fun γ hγ g => hleft γ hγ v g) (fun k hk g => hlev k hk v g) ?_
      (LinearMap.range F) inferInstance fun x hx => ⟨W.rep ⟨x, hx⟩ v, heqv ⟨x, hx⟩ v⟩
    intro g
    have h : (fun x : infU E a => F v (g * x)) = fun x : infU E a => f.1 v (g * x * e g) :=
      funext fun x => hinf x x.2 v g
    rw [h]
    exact (f.2.1 v).cont.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  exact ⟨⟨F, haut, heqv⟩, UpperTheory.Gal.Gen.mem_fixedBy.2 fun k hk v g => hlev k hk v g, fun _ _ => rfl⟩
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

private theorem mvEval_aeval_X_sub_C_eq_eval_sub {k : Type} [Field k] {σ : Type} (p : Polynomial k) (i : σ) (c : k)
    (z : σ → k) :
    MvPolynomial.eval z (Polynomial.aeval (MvPolynomial.X i - MvPolynomial.C c) p) =
      Polynomial.eval (z i - c) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp

private theorem norm_prod_sub_one_le_of_norm_sub_one_le {k : Type} [NormedField k] [IsUltrametricDist k] {ι : Type}
    [DecidableEq ι] (s : Finset ι) (f : ι → k) {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 1)
    (h : ∀ j ∈ s, ‖f j - 1‖ ≤ c) : ‖∏ j ∈ s, f j - 1‖ ≤ c := by
  induction s using Finset.induction_on with
  | empty => simpa using hc0
  | insert j s hj ih =>
    rw [Finset.prod_insert hj]
    have h1 := h j (Finset.mem_insert_self j s)
    have h2 := ih (fun l hl => h l (Finset.mem_insert_of_mem hl))
    have hx : ‖f j‖ ≤ 1 := by
      have := IsUltrametricDist.norm_add_le_max (f j - 1) 1
      rw [sub_add_cancel, norm_one] at this
      exact this.trans (max_le (h1.trans hc) le_rfl)
    have e : f j * ∏ l ∈ s, f l - 1 = f j * (∏ l ∈ s, f l - 1) + (f j - 1) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ h1)
    rw [norm_mul]
    calc ‖f j‖ * ‖∏ l ∈ s, f l - 1‖ ≤ 1 * c := mul_le_mul hx h2 (norm_nonneg _) zero_le_one
      _ = c := one_mul c

private theorem norm_one_sub_le_one_of_norm_le_one {k : Type} [NormedField k] [IsUltrametricDist k] {x : k}
    (h : ‖x‖ ≤ 1) : ‖1 - x‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_one]
  · rw [norm_neg]
    exact h

theorem UpperTheory.Gal.Wt.sepPoly_of :
    UpperTheory.Gal.Wt.Kapl → UpperTheory.Gal.Wt.SepPoly := by
  intro hK k _ _ σ _ Z₁ Z₂ h₁ h₂ hd ε hε
  classical
  obtain ⟨D, hD, hDd⟩ := hd.exists_thickenings h₁ h₂.isClosed
  have he0 : 0 < min ε 1 := lt_min hε one_pos
  have he1 : min ε 1 ≤ 1 := min_le_right _ _
  have heε : min ε 1 ≤ ε := min_le_left _ _
  obtain ⟨T, hTsub, hTfin, hcov⟩ := h₁.finite_cover_balls (mul_pos hD he0)
  obtain ⟨Y, hY, hmemY⟩ : ∃ Y : Set k, IsCompact Y ∧
      ∀ i, ∀ a ∈ hTfin.toFinset, ∀ z ∈ Z₁ ∪ Z₂, z i - a i ∈ Y := by
    refine ⟨⋃ i : σ, ⋃ a ∈ hTfin.toFinset, (fun z : σ → k => z i - a i) '' (Z₁ ∪ Z₂), ?_, ?_⟩
    · exact isCompact_iUnion fun i => hTfin.toFinset.isCompact_biUnion fun a _ =>
        (h₁.union h₂).image (by fun_prop)
    · intro i a ha z hz
      exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion₂.2 ⟨a, ha, z, hz, rfl⟩⟩
  obtain ⟨p, hp1, hp2, hp3⟩ := hK k Y hY D (min ε 1) hD he0 he1
  obtain ⟨q, hq⟩ : ∃ q : (σ → k) → MvPolynomial σ k,
      ∀ a z, MvPolynomial.eval z (q a) = ∏ i, Polynomial.eval (z i - a i) p :=
    ⟨fun a => ∏ i, Polynomial.aeval (MvPolynomial.X i - MvPolynomial.C (a i)) p,
      fun a z => by simp only [map_prod, mvEval_aeval_X_sub_C_eq_eval_sub]⟩
  have hqle : ∀ a ∈ hTfin.toFinset, ∀ z ∈ Z₁ ∪ Z₂, ‖MvPolynomial.eval z (q a)‖ ≤ 1 := by
    intro a ha z hz
    rw [hq, norm_prod]
    exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => hp1 _ (hmemY i a ha z hz))
  refine ⟨1 - ∏ a ∈ hTfin.toFinset, (1 - q a), ?_, ?_⟩
  · intro z hz
    obtain ⟨a0, ha0T, hza⟩ := Set.mem_iUnion₂.1 (hcov hz)
    have ha0 : a0 ∈ hTfin.toFinset := hTfin.mem_toFinset.2 ha0T
    have hnear : ‖MvPolynomial.eval z (q a0) - 1‖ ≤ min ε 1 := by
      rw [hq]
      apply norm_prod_sub_one_le_of_norm_sub_one_le _ _ he0.le he1
      intro i _
      apply hp3
      have := norm_le_pi_norm (z - a0) i
      rw [Metric.mem_ball, dist_eq_norm] at hza
      simp only [Pi.sub_apply] at this
      linarith
    simp only [map_sub, map_one, map_prod]
    rw [show (1 : k) - ∏ a ∈ hTfin.toFinset, (1 - MvPolynomial.eval z (q a)) - 1 =
        -∏ a ∈ hTfin.toFinset, (1 - MvPolynomial.eval z (q a)) by ring, norm_neg, norm_prod,
      ← Finset.mul_prod_erase _ _ ha0]
    have hrest : ∏ a ∈ hTfin.toFinset.erase a0, ‖1 - MvPolynomial.eval z (q a)‖ ≤ 1 := by
      apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
      intro a ha
      exact norm_one_sub_le_one_of_norm_le_one (hqle a (Finset.mem_of_mem_erase ha) z (Or.inl hz))
    have h0 : ‖1 - MvPolynomial.eval z (q a0)‖ ≤ min ε 1 := by
      rw [norm_sub_rev]
      exact hnear
    calc ‖1 - MvPolynomial.eval z (q a0)‖ *
          ∏ a ∈ hTfin.toFinset.erase a0, ‖1 - MvPolynomial.eval z (q a)‖
        ≤ min ε 1 * 1 := mul_le_mul h0 hrest (Finset.prod_nonneg fun _ _ => norm_nonneg _) he0.le
      _ ≤ ε := by linarith
  · intro z hz
    have hfar : ∀ a ∈ hTfin.toFinset, ‖MvPolynomial.eval z (q a)‖ ≤ min ε 1 := by
      intro a ha
      have hdist : D ≤ ‖z - a‖ := by
        by_contra hlt
        push_neg at hlt
        apply Set.disjoint_left.1 hDd
          (Metric.self_subset_thickening hD _ (hTsub (hTfin.mem_toFinset.1 ha)))
        exact Metric.mem_thickening_iff.2 ⟨z, hz, by rw [dist_eq_norm, norm_sub_rev]; exact hlt⟩
      obtain ⟨i, hi⟩ : ∃ i, D ≤ ‖z i - a i‖ := by
        by_contra hno
        push_neg at hno
        have := (pi_norm_lt_iff (x := z - a) hD).2 (fun i => by simpa using hno i)
        linarith
      rw [hq, norm_prod, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
      have h0 := hp2 _ (hmemY i a ha z (Or.inr hz)) hi
      have hrest : ∏ j ∈ Finset.univ.erase i, ‖Polynomial.eval (z j - a j) p‖ ≤ 1 :=
        Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun j _ => hp1 _ (hmemY j a ha z (Or.inr hz)))
      calc _ ≤ min ε 1 * 1 :=
            mul_le_mul h0 hrest (Finset.prod_nonneg fun _ _ => norm_nonneg _) he0.le
        _ = min ε 1 := mul_one _
    simp only [map_sub, map_one, map_prod]
    have := norm_prod_sub_one_le_of_norm_sub_one_le hTfin.toFinset (fun a => 1 - MvPolynomial.eval z (q a)) he0.le he1
      (fun a ha => by
        rw [show (1 : k) - MvPolynomial.eval z (q a) - 1 = -MvPolynomial.eval z (q a) by ring,
          norm_neg]
        exact hfar a ha)
    rw [norm_sub_rev]
    linarith
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

private theorem cEmb_fin {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (τ : E →+* ℂ) {c : UA E n}
    (hc : c ∈ finU (E := E) (n := n)) : cEmb τ c = 1 := by
  have : cInf c = 1 := hc
  simp [cEmb, this]

theorem UpperTheory.Gal.Wt.famEx_of : NeatLev → EllC → Twist → TwistBd → Kap0 → Pieces → DeltaNear → FamOf → FamEx := by
  intro hN hE hT hTB hK hP hD hF E _ _ _ l _ ι a ha w₀ hl hs v' hs' hap K hKl hKv Kv hKo W f hf τ hτ X b hb ε hε
  classical
  obtain ⟨C, hC, hKC, hneat, hint, hfC⟩ := hN E l Fact.out a ha w₀ hl hs v' hs' hap K hKl hKv Kv hKo W f hf
  obtain ⟨ℓ, hℓ⟩ := hE E a C hC.fin hneat
  obtain ⟨R, hR0, hR⟩ := hTB E l ι a C hC ℓ hℓ W f X b hb
  obtain ⟨κ, hκr, hκi, hκ1, hκc, hκI⟩ := hK E l ι a v' τ hτ
  haveI : CompactSpace C := isCompact_iff_compactSpace.1 hC.compact
  let φ : C →* GL (Fin a) ℂ := κ.comp C.subtype
  have hφI : ∀ c : C, IntGL ι (φ c) := fun c => hκI _ (hint _ c.2)
  obtain ⟨Q, _, c, P, hQ⟩ := hP l ι a C φ (fun i j => (hκc i j).comp continuous_subtype_val) hφI
    ((Kv.comap (cLoc v')).subgroupOf C)
    (hKo.preimage ((GlobalTheory.BCT.GlobLev.continuous_cLoc v').comp continuous_subtype_val))
    (fun x hx => by
      have h1 : cLoc v' x.1 = 1 := (hκ1 _).1 hx
      change cLoc v' x.1 ∈ Kv
      rw [h1]; exact Kv.one_mem) (ε / R) (div_pos hε hR0)
  choose F hFC hFv using fun q => hT E a C hC ℓ hℓ W f (c q)
  let M : UA E a → GL (Fin a) ℂ := fun g => (cEmb τ g)⁻¹ * κ g
  let n : UA E a → GL (Fin a) ℂ := fun g => φ (ℓ g) * (M g)⁻¹
  have hn : IsNrm τ C n := by
    refine ⟨fun γ hγ g => ?_, fun k hk g => ?_, fun x hx g => ?_⟩
    · simp only [n, M, hℓ.left γ hγ, map_mul, hκr γ hγ]
      group
    · have := hℓ.lev ⟨k, hk⟩ g
      have e : φ ⟨k, hk⟩ = κ k := rfl
      simp only [n, M] at this ⊢
      rw [this]
      simp only [map_mul, cEmb_fin τ (hC.fin hk), e]
      group
    · simp only [n, M, hℓ.inf x hx, map_mul, hκi x hx]
      group
  obtain ⟨d, hd⟩ := hF E a τ C hC n hn W Q F hFC P
  refine ⟨d, M, fun g h hh h1 => ?_, fun ν => ?_⟩
  · simp only [M, map_mul, cEmb_fin τ hh, (hκ1 h).2 h1, mul_one]
  have hfam := hd ν fun q => (φ (c q))⁻¹
  refine ⟨_, ⟨hfam.aut, fun k hk => hfam.fix k (hKC hk), hfam.inf, hfam.up, hfam.le, hfam.ge, hfam.fin⟩, fun g i => ?_⟩
  obtain ⟨q₀, h0, h1, h2, h3⟩ := hQ (ℓ g)
  have hnM : n g * M g = φ (ℓ g) := by simp only [n]; group
  have hε' : 0 ≤ ε / R := (div_pos hε hR0).le
  have hv : f.1 (b g i) g = (F q₀).1 (b g i) g := by
    rw [hFv, ← hfC ((c q₀)⁻¹ * ℓ g : C) ⟨Subtype.prop _, h0⟩ (b g i) (g * ((ℓ g)⁻¹ * c q₀ : C))]
    congr 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hδ : ∀ q, (φ (c q))⁻¹ * φ (ℓ g) = φ ((c q)⁻¹ * ℓ g) := fun q => by rw [map_mul, map_inv]
  rw [famOf_apply, hv, hnM]
  have e : (F q₀).1 (b g i) g - ∑ q, pev (P q) (φ (ℓ g)) * delta ν ((φ (c q))⁻¹ * φ (ℓ g)) * (F q).1 (b g i) g =
      ∑ q, ((if q = q₀ then 1 else 0) - pev (P q) (φ (ℓ g)) * delta ν (φ ((c q)⁻¹ * ℓ g))) * (F q).1 (b g i) g := by
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, hδ]

  rw [e, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hε.le fun q _ => ?_
  rw [map_mul, norm_mul, hFv, ← div_mul_cancel₀ ε hR0.ne']
  refine mul_le_mul ?_ (hR _ _ _) (norm_nonneg _) hε'
  obtain ⟨hb1, hb2⟩ := hD l ι a ν _ (hφI ((c q)⁻¹ * ℓ g))
  by_cases hq : q = q₀
  · subst hq
    have hb3 := hb2 _ hε' h1
    rw [if_pos rfl]
    have e2 : 1 - pev (P q) (φ (ℓ g)) * delta ν (φ ((c q)⁻¹ * ℓ g)) =
        -((pev (P q) (φ (ℓ g)) - 1) * delta ν (φ ((c q)⁻¹ * ℓ g)) + (delta ν (φ ((c q)⁻¹ * ℓ g)) - 1)) := by ring
    rw [e2, map_neg, norm_neg, map_add (f := _)]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hb3)
    rw [map_mul, norm_mul]
    exact (mul_le_mul h2 hb1 (norm_nonneg _) hε').trans_eq (mul_one _)
  · rw [if_neg hq, zero_sub, map_neg, norm_neg, map_mul, norm_mul]
    exact (mul_le_mul (h3 q hq) hb1 (norm_nonneg _) hε').trans_eq (mul_one _)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

private theorem tor_one (a k : ℕ) : tor a k 1 = 1 := by
  apply Units.ext
  rw [tor_coe]
  simp

private theorem top_ne {a : ℕ} (κ : DomWeight a) : top κ ≠ 0 := by
  intro h
  have h1 : extremal ℂ a κ = 0 := congrArg Subtype.val h
  exact Formalism.GradedWeylDivisibility.hwNe ℂ a a le_rfl _ h1

private theorem exists_dual {a : ℕ} {κ : DomWeight a} {w : nablaSq ℂ a κ} (hw : w ≠ 0) :
    ∃ L : nablaSq ℂ a κ →ₗ[ℂ] ℂ, L w ≠ 0 := by
  by_contra hc
  push Not at hc
  exact hw ((Module.forall_dual_apply_eq_zero_iff ℂ w).1 hc)

private theorem span_top {a : ℕ} {κ : DomWeight a} (A : Set (nablaSq ℂ a κ)) (hA : ∃ w ∈ A, w ≠ 0)
    (hst : ∀ u : Matrix.unitaryGroup (Fin a) ℂ, ∀ w ∈ A, sqRep ℂ a κ (unitaryIncl a u) w ∈ A) :
    Submodule.span ℂ A = ⊤ := by
  let S : Subrepresentation (smallRep (unitaryIncl a) κ) :=
    ⟨Submodule.span ℂ A, fun u x hx => by
      change sqRep ℂ a κ (unitaryIncl a u) x ∈ Submodule.span ℂ A
      induction hx using Submodule.span_induction with
      | mem x h => exact Submodule.subset_span (hst u x h)
      | zero => simp
      | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx⟩
  rcases (isIrreducible_smallRep_unitary a κ).eq_bot_or_eq_top S with h | h
  · exfalso
    obtain ⟨w, hw, hw0⟩ := hA
    have h1 : Submodule.span ℂ A = ⊥ := congrArg Subrepresentation.toSubmodule h
    exact hw0 ((Submodule.span_eq_bot.1 h1) w hw)
  · exact congrArg Subrepresentation.toSubmodule h

theorem UpperTheory.Gal.Wt.wtBd_of :
    UpperTheory.Gal.Wt.ExpBasic → UpperTheory.Gal.Wt.ExpDisj → UpperTheory.Gal.Wt.SqExp → UpperTheory.Gal.Wt.TopUp → UpperTheory.Gal.Wt.TorFacts → UpperTheory.Gal.Wt.WtBd := by
  intro hB hD hS hT hF a k κ s
  have hz1 : ∀ f : Circle → ℂ, f = 0 → f 1 = 0 := fun f h => by rw [h]; rfl
  refine ⟨fun A hA hst hexp => ?_, fun w hw hexp => ?_⟩
  · have htop : Submodule.span ℂ A = ⊤ := span_top A hA hst
    by_contra hlt
    push Not at hlt
    obtain ⟨L, hL⟩ := exists_dual (top_ne κ)
    have hall : ∀ x ∈ Submodule.span ℂ A, (fun z => L (sqRep ℂ a κ (tor a k z) x)) ∈ ExpLe s := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x h => exact hexp x h L
      | zero =>
        have h0 := (ExpLe s).zero_mem
        convert h0 using 1
        funext z
        simp only [map_zero, Pi.zero_apply]
      | add x y _ _ hx hy =>
        have := (ExpLe s).add_mem hx hy
        convert this using 1
        funext z
        simp only [map_add, Pi.add_apply]
      | smul c x _ hx =>
        have := (ExpLe s).smul_mem c hx
        convert this using 1
        funext z
        simp only [map_smul, Pi.smul_apply]
    have hmem := hall (top κ) (htop.ge Submodule.mem_top)
    have hfun : (fun z => L (sqRep ℂ a κ (tor a k z) (top κ))) = fun z : Circle => L (top κ) * (z : ℂ) ^ psum κ k := by
      funext z
      obtain ⟨hup, -, hchi, -⟩ := hF a k z
      rw [hT a κ _ hup, hchi κ, map_smul, smul_eq_mul, mul_comm]
    rw [hfun] at hmem
    have hge := (hB.2.2.2.1 (L (top κ)) (psum κ k)).2
    have h0 := hz1 _ (hD s (psum κ k) _ hlt hmem hge)
    simp at h0
    exact hL h0
  · by_contra hlt
    push Not at hlt
    obtain ⟨L, hL⟩ := exists_dual hw
    have h0 := hz1 _ (hD (psum κ k) s _ hlt (hS a k κ w L).1 (hexp L))
    simp only [tor_one, map_one, Module.End.one_apply] at h0
    exact hL h0
end
