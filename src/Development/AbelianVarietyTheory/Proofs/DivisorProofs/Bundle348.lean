module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Mathlib.RingTheory.Derivation.Basic
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle066
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle018
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle271
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Presheaf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TangentEqLcZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtOrderProdSub

@[expose] public section

section

set_option autoImplicit false

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.PDA

theorem PDPoly.isDPMorphism_of_isStd :
    ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J)),
      Q.IsStd δ η → ∀ (C : Type) [CommRing C] (J'' : Ideal C) (δ'' : DividedPowers J'') (F : Q.P →+* C) (c : C),
        c ∈ J'' → IsDPMorphism δ δ'' (F.comp (algebraMap B Q.P)) → (∀ n, F (Q.e n) = δ''.dpow n c) →
          IsDPMorphism η δ'' F := by
  intro B _ J δ Q η hQ C _ J'' δ'' F c hc hF he
  have hS : Q.ext J = Ideal.span (algebraMap B Q.P '' J ∪ Set.range fun n : ℕ ↦ Q.e (n + 1)) := by
    rw [Ideal.span_union, ← Ideal.map_span, Ideal.span_eq]; rfl
  refine IsDPMorphism.on_span η δ'' hS ?_ ?_
  · rintro s (⟨a, ha, rfl⟩ | ⟨k, rfl⟩)
    · exact hF.1 (Ideal.mem_map_of_mem _ ha)
    · rw [he]; exact δ''.dpow_mem k.succ_ne_zero hc
  · rintro n s (⟨a, ha, rfl⟩ | ⟨k, rfl⟩)
    · rw [hQ.dp.2 a ha]
      exact (hF.2 a ha).symm
    · have h1 := Q.e_one_mem_ext J
      show F (η.dpow n (Q.e (k + 1))) = δ''.dpow n (F (Q.e (k + 1)))
      have h2 : η.dpow n (Q.e (k + 1)) = (n.uniformBell (k + 1) : Q.P) * Q.e (n * (k + 1)) := by
        rw [← hQ.var (k + 1), η.dpow_comp k.succ_ne_zero h1, hQ.var]
      rw [h2, map_mul, map_natCast, he, he, δ''.dpow_comp k.succ_ne_zero hc]

end GlobalTheory.PDA
end

section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory

theorem exists_pdPoly : ∀ (B : Type) [CommRing B], Nonempty (PDPoly B) :=
  fun B _ ↦ ⟨stdPoly B⟩

end GlobalTheory
end

section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.DerFil

theorem fil_succ_le {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (N : ℕ) :
    fil δ (N + 1) ≤ fil δ N :=
  Ideal.span_mono fun _ ⟨l, h1, h2, h3⟩ ↦ ⟨l, h1, by omega, h3⟩

theorem prod_mem_fil {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (N : ℕ)
    (l : List (ℕ × B)) (hl : ∀ p ∈ l, p.2 ∈ J) (hN : N ≤ (l.map Prod.fst).sum) :
    (l.map fun p ↦ δ.dpow p.1 p.2).prod ∈ fil δ N :=
  Ideal.subset_span ⟨l, hl, hN, rfl⟩

theorem smul_deriv_prod_mem {R B M : Type} [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module B M] [Module R M] [IsScalarTower R B M] (J : Ideal B) (δ : DividedPowers J)
    (D : Derivation R B M) (N₀ : Submodule B M)
    (hD : ∀ n, ∀ a ∈ J, D (δ.dpow (n + 1) a) - δ.dpow n a • D a ∈ N₀) (N : ℕ) :
    ∀ (l : List (ℕ × B)), (∀ p ∈ l, p.2 ∈ J) → ∀ (l' : List (ℕ × B)), (∀ p ∈ l', p.2 ∈ J) →
      N + 1 ≤ (l'.map Prod.fst).sum + (l.map Prod.fst).sum →
      (l'.map fun p ↦ δ.dpow p.1 p.2).prod • D ((l.map fun p ↦ δ.dpow p.1 p.2).prod) ∈
        fil δ N • (⊤ : Submodule B M) ⊔ N₀ := by
  intro l
  induction l with
  | nil => intro _ l' _ _; simp
  | cons p l ih =>
    intro hl l' hl' hs
    have hp : p.2 ∈ J := hl p (by simp)
    have hl2 : ∀ q ∈ l, q.2 ∈ J := fun q hq ↦ hl q (by simp [hq])
    simp only [List.map_cons, List.prod_cons, List.sum_cons] at hs ⊢
    rw [Derivation.leibniz, smul_add, smul_smul, smul_smul]
    refine add_mem ?_ ?_
    · have hl3 : ∀ q ∈ p :: l', q.2 ∈ J := by
        intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact hp
        · exact hl' q hq
      have := ih hl2 (p :: l') hl3 (by simp only [List.map_cons, List.sum_cons]; omega)
      simpa only [List.map_cons, List.prod_cons, mul_comm] using this
    · rcases p with ⟨k, x⟩
      cases k with
      | zero => simp [δ.dpow_zero hp]
      | succ m =>
        have h := hD m x hp
        set c := (l'.map fun p ↦ δ.dpow p.1 p.2).prod * (l.map fun p ↦ δ.dpow p.1 p.2).prod
        have e : c • D (δ.dpow (m + 1) x) =
            c • (D (δ.dpow (m + 1) x) - δ.dpow m x • D x) + (c * δ.dpow m x) • D x := by
          rw [smul_sub, smul_smul, sub_add_cancel]
        rw [e]
        refine add_mem (Submodule.mem_sup_right (N₀.smul_mem _ h)) (Submodule.mem_sup_left ?_)
        refine Submodule.smul_mem_smul ?_ Submodule.mem_top
        have hm := prod_mem_fil δ N (l' ++ (m, x) :: l)
          (by
            intro q hq
            rcases List.mem_append.1 hq with hq | hq
            · exact hl' q hq
            · rcases List.mem_cons.1 hq with rfl | hq
              · exact hp
              · exact hl2 q hq)
          (by simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons] at hs ⊢; omega)
        simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons] at hm
        convert hm using 1
        simp only [c]; ring

end GlobalTheory.DerFil


open GlobalTheory.DerFil in
theorem GlobalTheory.DerFil.deriv_fil_succ_le : ∀ (R B M : Type) [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module B M] [Module R M] [IsScalarTower R B M] (J : Ideal B) (δ : DividedPowers J) (D : Derivation R B M)
    (N₀ : Submodule B M), (∀ n, ∀ a ∈ J, D (δ.dpow (n + 1) a) - δ.dpow n a • D a ∈ N₀) →
    ∀ N, ∀ x ∈ fil δ (N + 1), D x ∈ fil δ N • (⊤ : Submodule B M) ⊔ N₀ := by
  intro R B M _ _ _ _ _ _ _ J δ D N₀ hD N x hx
  induction hx using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨l, hl, hs, rfl⟩ := hb
    simpa using smul_deriv_prod_mem J δ D N₀ hD N l hl [] (by simp) (by simpa using hs)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x hx ih =>
    rw [smul_eq_mul, Derivation.leibniz]
    exact add_mem (Submodule.smul_mem _ _ ih)
      (Submodule.mem_sup_left (Submodule.smul_mem_smul (fil_succ_le δ N hx) Submodule.mem_top))
end

section

open ReciprocityTheory.PGsh GlobalTheory.FGDepth

theorem _root_.GlobalTheory.T.exists_integral_dual_frame_of_isSatFrame : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (i d : ℕ) (u : Fin i → Fin d → C), IsSatFrame v u → ∃ l : Fin i → Fin d → C, (∀ a e, IsIntV v (l a e)) ∧ ∀ a a', ∑ e, l a e * u a' e = if a = a' then 1 else 0 := by
  first | exact @GlobalTheory.FrameDual.frameDual | exact GlobalTheory.FrameDual.frameDual | (intros; apply GlobalTheory.FrameDual.frameDual <;> assumption)
end

section

namespace GlobalTheory.FGDepth.Coord

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

noncomputable section

variable {C : Type} [Field C]

open MvPowerSeries in
private lemma subst_sum_smul_X' {C : Type} [Field C] {σ τ ι : Type} [Fintype ι]
    {b : σ → MvPowerSeries τ C} (hb : HasSubst b) (c : ι → C) (g : ι → σ) :
    subst b (∑ a, c a • (X (g a) : MvPowerSeries σ C)) = ∑ a, c a • b (g a) := by

  rw [← coe_substAlgHom hb, map_sum]
  simp only [map_smul, coe_substAlgHom, subst_X hb]

open MvPowerSeries in
private lemma mvIsInt_X_divisor {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {σ : Type}
    (s : σ) : _root_.ReciprocityTheory.PGsh.MvIsInt v (X s : MvPowerSeries σ C) := by
  classical
  intro α
  show 0 ≤ v (coeff α (X s : MvPowerSeries σ C))
  rw [coeff_X]
  split_ifs <;> simp


open MvPowerSeries in
variable {C : Type} [Field C] in
theorem _root_.GlobalTheory.FGDepth.Coord.depth_in_coords : ∀ (C : Type) [Field C] [CharZero C]
    (v : AddValuation C (WithTop ℝ)) (i d c : ℕ) (G : _root_.ReciprocityTheory.PGsh.LogFGL v d) (u : Fin i → Fin d → C)
    (Φ Ψ : Fin d → MvPowerSeries (Fin d) C),
    (∀ a, _root_.ReciprocityTheory.PGsh.MvIsInt v (Φ a) ∧ constantCoeff (Φ a) = 0 ∧ _root_.ReciprocityTheory.PGsh.MvIsInt v (Ψ a) ∧
      constantCoeff (Ψ a) = 0) →
    (∀ a, subst Ψ (Φ a) = X a ∧ subst Φ (Ψ a) = X a) →
    ∀ (t : Fin d → MvPowerSeries (Fin i) C), (∀ a, constantCoeff (t a) = 0) →
    (∀ e, subst t (subst Φ (G.lg e)) = ∑ a, u a e • X a) →
    _root_.GlobalTheory.FGDepth.detDepth G u c = ⨅ f : {f : MvPowerSeries (Σ _ : Fin i, Fin d) C //
      _root_.ReciprocityTheory.PGsh.MvIsInt v f}, _root_.GlobalTheory.FGDepth.toE (v (_root_.GlobalTheory.FGDepth.derivAt0
        (_root_.GlobalTheory.FGDepth.detPow C i c) (subst (fun x : (Σ _ : Fin i, Fin d) =>
          subst (fun a : Fin i => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (t x.2))
            f.1))) := by
  intro C _ _ v i d c G u Φ Ψ hΦΨ hinv t ht0 ht
  have hΦ : HasSubst Φ := hasSubst_of_constantCoeff_zero fun a => (hΦΨ a).2.1
  have hΨ : HasSubst Ψ := hasSubst_of_constantCoeff_zero fun a => (hΦΨ a).2.2.2
  have htS : HasSubst t := hasSubst_of_constantCoeff_zero ht0
  have hlg : HasSubst G.lg := hasSubst_of_constantCoeff_zero G.2
  have hex0 : ∀ a, constantCoeff (_root_.GlobalTheory.FGDepth.expOf G a) = 0 := (_root_.GlobalTheory.FGDepth.isExp_expOf G).1
  have hexS : HasSubst (_root_.GlobalTheory.FGDepth.expOf G) := hasSubst_of_constantCoeff_zero hex0
  have hLin0 : ∀ e, constantCoeff (∑ a, u a e • (X a : MvPowerSeries (Fin i) C)) = 0 := by
    intro e

    simp [map_sum]
  have hLinS : HasSubst fun e => ∑ a, u a e • (X a : MvPowerSeries (Fin i) C) :=
    hasSubst_of_constantCoeff_zero hLin0
  have hΦtS : HasSubst fun a => subst t (Φ a) :=
    hasSubst_of_constantCoeff_zero fun a => constantCoeff_subst_eq_zero htS ht0 (hΦΨ a).2.1

  have hΦt : ∀ a, subst t (Φ a) =
      subst (fun e => ∑ b, u b e • (X b : MvPowerSeries (Fin i) C))
        (_root_.GlobalTheory.FGDepth.expOf G a) := by
    intro a
    have h1 : (fun e => ∑ b, u b e • (X b : MvPowerSeries (Fin i) C)) =
        fun e => subst (fun a => subst t (Φ a)) (G.lg e) := by
      funext e
      rw [← subst_comp_subst_apply hΦ htS, ht]
    rw [h1, ← subst_comp_subst_apply hlg hΦtS, _root_.GlobalTheory.FGDepth.subst_lg_expOf, subst_X hΦtS]
  have ht_eq : ∀ e, t e = subst (fun e => ∑ b, u b e • (X b : MvPowerSeries (Fin i) C))
      (subst (_root_.GlobalTheory.FGDepth.expOf G) (Ψ e)) := by
    intro e
    rw [subst_comp_subst_apply hexS hLinS]
    calc t e = subst t (X e) := (subst_X htS e).symm
      _ = subst t (subst Φ (Ψ e)) := by rw [(hinv e).2]
      _ = subst (fun a => subst t (Φ a)) (Ψ e) := subst_comp_subst_apply hΦ htS _
      _ = _ := by simp_rw [hΦt]

  have hXb : ∀ b : Fin i, HasSubst fun a : Fin i =>
      (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C) :=
    fun b => hasSubst_of_constantCoeff_zero fun a => constantCoeff_X _
  have hXd : ∀ b : Fin i, HasSubst fun a : Fin d =>
      (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C) :=
    fun b => hasSubst_of_constantCoeff_zero fun a => constantCoeff_X _
  have hLinB0 : ∀ (b : Fin i) (e : Fin d),
      constantCoeff (∑ a, u a e • (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) = 0 := by
    intro b e

    simp [map_sum]
  have hLinBS : ∀ b : Fin i, HasSubst fun e =>
      ∑ a, u a e • (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C) :=
    fun b => hasSubst_of_constantCoeff_zero (hLinB0 b)
  have hE0 : ∀ x, constantCoeff
      (_root_.GlobalTheory.FGDepth.expAlong (fun _ : Fin i => G) (fun _ : Fin i => u) x) = 0 :=
    fun x => constantCoeff_subst_eq_zero (hLinBS x.1) (hLinB0 x.1) (hex0 x.2)
  have hES : HasSubst
      (_root_.GlobalTheory.FGDepth.expAlong (fun _ : Fin i => G) (fun _ : Fin i => u)) :=
    hasSubst_of_constantCoeff_zero hE0
  have hΨ0 : ∀ x : (Σ _ : Fin i, Fin d), constantCoeff
      (subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Ψ x.2)) = 0 :=
    fun x => constantCoeff_subst_eq_zero (hXd x.1) (fun a => constantCoeff_X _) (hΦΨ x.2).2.2.2
  have hΨS : HasSubst fun x : (Σ _ : Fin i, Fin d) =>
      subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Ψ x.2) :=
    hasSubst_of_constantCoeff_zero hΨ0
  have hΦ0 : ∀ x : (Σ _ : Fin i, Fin d), constantCoeff
      (subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Φ x.2)) = 0 :=
    fun x => constantCoeff_subst_eq_zero (hXd x.1) (fun a => constantCoeff_X _) (hΦΨ x.2).2.1
  have hΦS : HasSubst fun x : (Σ _ : Fin i, Fin d) =>
      subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Φ x.2) :=
    hasSubst_of_constantCoeff_zero hΦ0

  have key : ∀ x : (Σ _ : Fin i, Fin d),
      subst (fun a : Fin i => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (t x.2) =
      subst (_root_.GlobalTheory.FGDepth.expAlong (fun _ : Fin i => G) (fun _ : Fin i => u))
        (subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C))
          (Ψ x.2)) := by
    rintro ⟨b, e⟩
    have hlin : (fun e' => subst (fun a : Fin i =>
        (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C))
          (∑ a, u a e' • (X a : MvPowerSeries (Fin i) C))) =
        fun e' => ∑ a, u a e' • (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C) := by
      funext e'
      exact subst_sum_smul_X' (hXb b) (fun a => u a e') id
    rw [ht_eq e, subst_comp_subst_apply hLinS (hXb b), hlin,
      subst_comp_subst_apply hexS (hLinBS b), subst_comp_subst_apply (hXd b) hES]
    congr 1
    funext a
    rw [subst_X hES]
    rfl

  have hround : (fun x : (Σ _ : Fin i, Fin d) => subst
      (fun x : (Σ _ : Fin i, Fin d) =>
        subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Ψ x.2))
      (subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Φ x.2))) =
      X := by
    funext x
    rw [subst_comp_subst_apply (hXd x.1) hΨS]
    simp_rw [subst_X hΨS]
    rw [← subst_comp_subst_apply hΨ (hXd x.1), (hinv x.2).1, subst_X (hXd x.1)]
  unfold _root_.GlobalTheory.FGDepth.detDepth _root_.GlobalTheory.FGDepth.depth
  simp_rw [key]
  apply le_antisymm
  · refine le_iInf fun f => ?_
    rw [← subst_comp_subst_apply hΨS hES]
    exact iInf_le_of_le ⟨_, _root_.ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v f.2
      (fun x => _root_.ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v (hΦΨ x.2).2.2.1 (fun a => mvIsInt_X_divisor v _) (fun a => constantCoeff_X _))
      hΨ0⟩ le_rfl
  · refine le_iInf fun f => ?_
    refine iInf_le_of_le ⟨_, _root_.ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v f.2
      (fun x => _root_.ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v (hΦΨ x.2).1 (fun a => mvIsInt_X_divisor v _) (fun a => constantCoeff_X _))
      hΦ0⟩ ?_
    rw [← subst_comp_subst_apply hΨS hES, subst_comp_subst_apply hΦS hΨS, hround, subst_self]
    rfl

end

end GlobalTheory.FGDepth.Coord
end

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem expOf_twoSided_unique : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ))
    (d : ℕ) (G : LogFGL v d), IsExp G (expOf G) ∧ (∀ a, subst G.lg (expOf G a) = X a) ∧
      ∀ ex, IsExp G ex → ex = expOf G := by
  intro C _ _ v d G
  obtain ⟨h1, h2, h3⟩ := expOf_spec G
  exact ⟨h1, h3, h2⟩

end GlobalTheory.FGDepth
end

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.DetPowShape

noncomputable def detZ (i : ℕ) : MvPolynomial (Σ _ : Fin i, Fin i) ℤ :=
  Matrix.det (Matrix.of fun a b : Fin i =>
    (MvPolynomial.X ⟨b, a⟩ : MvPolynomial (Σ _ : Fin i, Fin i) ℤ))

theorem detPow_eq_map (C : Type) [Field C] (i c : ℕ) :
    detPow C i c = MvPolynomial.map (Int.castRingHom C) (detZ i ^ c) := by
  rw [map_pow, detZ, RingHom.map_det]
  unfold detPow
  congr 2
  ext a b
  simp [RingHom.mapMatrix_apply]

theorem weight_eq_sum {i : ℕ} (w : (Σ _ : Fin i, Fin i) → ℕ) (α : (Σ _ : Fin i, Fin i) →₀ ℕ) :
    Finsupp.weight w α = ∑ x, α x * w x := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [smul_eq_mul]

theorem det_wh {R : Type} [CommRing R] {i : ℕ} (w : (Σ _ : Fin i, Fin i) → ℕ)
    (hw : ∀ σ : Equiv.Perm (Fin i), ∑ j, w ⟨j, σ j⟩ = 1) :
    MvPolynomial.IsWeightedHomogeneous w (Matrix.det (Matrix.of fun a b : Fin i =>
      (MvPolynomial.X ⟨b, a⟩ : MvPolynomial (Σ _ : Fin i, Fin i) R))) 1 := by
  rw [Matrix.det_apply']
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  have hp := MvPolynomial.IsWeightedHomogeneous.prod (R := R) (w := w) Finset.univ
    (fun j => (MvPolynomial.X ⟨j, σ j⟩ : MvPolynomial (Σ _ : Fin i, Fin i) R))
    (fun j => w ⟨j, σ j⟩) (fun j _ => MvPolynomial.isWeightedHomogeneous_X R w _)
  rw [hw σ] at hp
  have hc : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Σ _ : Fin i, Fin i) R) =
      MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : R) := by simp
  simp only [Matrix.of_apply]
  rw [hc]
  simpa using hp.C_mul ((Equiv.Perm.sign σ : ℤ) : R)

theorem sum_of_mem_support {C : Type} [Field C] {i c : ℕ} (w : (Σ _ : Fin i, Fin i) → ℕ)
    (hw : ∀ σ : Equiv.Perm (Fin i), ∑ j, w ⟨j, σ j⟩ = 1) (α) (hα : α ∈ (detPow C i c).support) :
    ∑ x, α x * w x = c := by
  have h := (det_wh (R := C) w hw).pow c
  rw [← weight_eq_sum]
  have := h (MvPolynomial.mem_support_iff.1 hα)
  simpa using this

theorem detPow_shape : ∀ (C : Type) [Field C] [CharZero C] (i c : ℕ),
    (detPow C i c).IsHomogeneous (i * c) ∧ (∀ α, ∃ n : ℤ, (detPow C i c).coeff α = n) ∧
    (detPow C i c).coeff (∑ a : Fin i, Finsupp.single ⟨a, a⟩ c) = 1 ∧
    ∀ α ∈ (detPow C i c).support, (∀ a : Fin i, ∑ b : Fin i, α ⟨b, a⟩ = c) ∧
      (∀ b : Fin i, ∑ a : Fin i, α ⟨b, a⟩ = c) := by
  intro C _ _ i c
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := (GlobalTheory.LeadingMinors.isHomogeneous_det_X (k := C)
      (fun a b : Fin i => (⟨b, a⟩ : Σ _ : Fin i, Fin i))).pow c
    simpa [Fintype.card_fin, detPow] using this
  · intro α
    exact ⟨(detZ i ^ c).coeff α, by rw [detPow_eq_map, MvPolynomial.coeff_map]; simp⟩
  · let f : Fin i → (Σ _ : Fin i, Fin i) := fun a => ⟨a, a⟩
    have hf : Function.Injective f := fun x y h => congrArg Sigma.fst h
    have h1 : (∑ a : Fin i, Finsupp.single (⟨a, a⟩ : Σ _ : Fin i, Fin i) c) =
        Finsupp.mapDomain f (∑ a : Fin i, Finsupp.single a c) := by
      change _ = Finsupp.mapDomain.addMonoidHom f _

      simp [map_sum, f]
    have h2 : MvPolynomial.killCompl hf (detPow C i c) =
        MvPolynomial.monomial (∑ a : Fin i, Finsupp.single a c) 1 := by
      unfold detPow
      rw [map_pow, GlobalTheory.LeadingMinors.killCompl_det_X (k := C) hf
        (fun a b : Fin i => (⟨b, a⟩ : Σ _ : Fin i, Fin i)) id (fun a => rfl),
        MvPolynomial.monomial_pow, one_pow]
      · congr 1
        rw [Finset.smul_sum]
        simp
      · rintro a b hab ⟨x, hx⟩
        obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.1 hx
        exact hab ((eq_of_heq h2).symm.trans h1)
    rw [h1, ← MvPolynomial.coeff_killCompl hf, h2, MvPolynomial.coeff_monomial, if_pos rfl]
  · intro α hα
    constructor
    · intro a
      have h := sum_of_mem_support (C := C) (c := c)
        (fun x => if x.2 = a then 1 else 0) (fun σ => by
          rw [← Equiv.sum_comp σ.symm]
          simp) α hα
      rw [Fintype.sum_sigma] at h
      simpa using h
    · intro b
      have h := sum_of_mem_support (C := C) (c := c)
        (fun x => if x.1 = b then 1 else 0) (fun σ => by simp) α hα
      rw [Fintype.sum_sigma] at h
      simpa using h

end GlobalTheory.DetPowShape
end

section

open Polynomial

theorem _root_.GlobalTheory.T.exists_small_conjFixed_of_valuation : ∀ (K : GlobalTheory.UnitLemma.UQ) (k : ℕ), 1 ≤ k → ∃ t : K.O, K.Small t ∧ GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k := by
  first | exact @GlobalTheory.UnitLemma.exists_small_val | exact GlobalTheory.UnitLemma.exists_small_val | (intros; apply GlobalTheory.UnitLemma.exists_small_val <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.sections_isFractionRing_stalk_imageOfGenericPoint : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsIntegral Y] [GlobalTheory.IsNormalScheme Z] (U : Z.Opens), IsAffineOpen U →
    (U : Set Z) ⊆ Set.range π → ∀ h : GlobalTheory.NormSheafDescent.genPt π ∈ U,
    IsDomain Γ(Z, U) ∧ (letI := GlobalTheory.NormSheafDescent.algAK π U h
      IsFractionRing Γ(Z, U) (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π))) := by
  first | exact @GlobalTheory.NormSheafDescent.sections_isDomain_isFractionRing_stalk | exact GlobalTheory.NormSheafDescent.sections_isDomain_isFractionRing_stalk | (intros; apply GlobalTheory.NormSheafDescent.sections_isDomain_isFractionRing_stalk <;> assumption)
end
