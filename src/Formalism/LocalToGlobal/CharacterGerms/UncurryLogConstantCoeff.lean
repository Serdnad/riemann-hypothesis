module

import Formalism.LocalToGlobal.CharacterGerms.RowTiePCartSelfSt
public import Formalism.LocalToGlobal.CharacterGerms.GeneralGermZero
public import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import all Formalism.LocalToGlobal.CharacterGerms.AbstractGermZeroCondition
import all Formalism.LocalToGlobal.CharacterGerms.CoeffSingleSubstOfLowDegree

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds
namespace SelfConjugateGermZero

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ FormalGermZero GeneralGermZero

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

private theorem cc_subst_lemma {σ τ A : Type} [Finite σ] [CommRing A] (a : σ → MvPowerSeries τ A)
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ A) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = MvPowerSeries.constantCoeff f := by
  apply _root_.Formalism.L2.FormalSeriesBounds.AbstractGermZero.cc_subst_lemma <;> assumption

theorem hasSubst_col (col : Fin 2) :
    MvPowerSeries.HasSubst (fun x : Fin dd => (MvPowerSeries.X (col, x) : MvPowerSeries (Fin 2 × Fin dd) C)) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)

def lawS (Y : FBChart C V O dd) (x : Fin 2 × Fin dd) : MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C :=
  MvPowerSeries.subst (fun q : Fin 2 × Fin dd =>
    (MvPowerSeries.X (q.1, (x.1, q.2)) : MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C)) (Y.B.G.F x.2)

theorem hasSubst_tau (col : Fin 2) : MvPowerSeries.HasSubst (fun q : Fin 2 × Fin dd =>
    (MvPowerSeries.X (q.1, (col, q.2)) : MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C)) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)

theorem lawS_const (Y : FBChart C V O dd) (x : Fin 2 × Fin dd) : MvPowerSeries.constantCoeff (lawS Y x) = 0 := by
  unfold lawS
  rw [cc_subst_lemma (fun q : Fin 2 × Fin dd =>
    (MvPowerSeries.X (q.1, (x.1, q.2)) : MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C)) (fun _ => by simp)]
  exact Y.B.G.const x.2

theorem lawS_int (Y : FBChart C V O dd) (x : Fin 2 × Fin dd) : IntS V (lawS Y x) := by
  unfold lawS
  rw [AbstractGermZero.intS_iff_alt]
  exact AltInv.intS_subst (v := V.v) (fun _ => by simp)
    (fun q => (AbstractGermZero.intS_iff_alt V _).mp (FormalGermZero.intS_X _)) ((AbstractGermZero.intS_iff_alt V _).mp (Y.intF x.2))

theorem uncurry_log_constantCoeff (Y : FBChart C V O dd) (j : Fin dd) : MvPowerSeries.constantCoeff (un1 (Y.lg j)) = 0 := by
  show MvPowerSeries.coeff (Finsupp.mapDomain (fun x : Fin dd => ((0 : Fin 1), x)) 0) (Y.lg j) = 0
  rw [Finsupp.mapDomain_zero, Y.lg_lin j 0 (by simp)]
  simp

private theorem prod_X_lemma {σ τ A : Type} [CommRing A] (e : σ → τ) (d : σ →₀ ℕ) :
    (d.prod fun s n => (MvPowerSeries.X (e s) : MvPowerSeries τ A) ^ n) =
      MvPowerSeries.monomial (d.mapDomain e) 1 := by
  apply _root_.Formalism.L2.FormalSeriesBounds.FormalGermZero.prod_X_lemma_8 <;> assumption

private theorem un1_lift_lemma_2 (f : MvPowerSeries (Fin 1 × Fin dd) C) :
    MvPowerSeries.subst (fun i : Fin dd => (MvPowerSeries.X ((0 : Fin 1), i) : MvPowerSeries (Fin 1 × Fin dd) C))
      (un1 f) = f := by
  classical
  ext μ
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp))]
  simp only [prod_X_lemma (Prod.mk (0 : Fin 1)), MvPowerSeries.coeff_monomial]
  have hμ : (μ.mapDomain Prod.snd).mapDomain (Prod.mk (0 : Fin 1)) = μ := by
    rw [← Finsupp.mapDomain_comp]
    have hc : (Prod.mk (0 : Fin 1) ∘ (Prod.snd : Fin 1 × Fin dd → Fin dd)) = id := by
      funext p
      exact Prod.ext (Subsingleton.elim _ _) rfl
    rw [hc, Finsupp.mapDomain_id]
  rw [finsum_eq_single _ (μ.mapDomain Prod.snd)]
  · rw [if_pos hμ.symm, smul_eq_mul, mul_one]
    show MvPowerSeries.coeff ((μ.mapDomain Prod.snd).mapDomain (fun x : Fin dd => ((0 : Fin 1), x))) f = _
    rw [show (fun x : Fin dd => ((0 : Fin 1), x)) = Prod.mk (0 : Fin 1) from rfl, hμ]
  · intro d hd
    rw [if_neg, smul_zero]
    intro h
    apply hd
    rw [h, ← Finsupp.mapDomain_comp,
      show (Prod.snd ∘ Prod.mk (0 : Fin 1) : Fin dd → Fin dd) = id from rfl, Finsupp.mapDomain_id]

private theorem ev1_lemma_3 {n : ℕ} (Q : Pt C n dd) (hQ : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0)
    (f : PS C 1 dd) : ev ![Q] f = MvPowerSeries.subst Q (un1 f) := by
  have hA : MvPowerSeries.HasSubst
      (fun i : Fin dd => (MvPowerSeries.X ((0 : Fin 1), i) : MvPowerSeries (Fin 1 × Fin dd) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hB : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin dd => (![Q] : Fin 1 → Pt C n dd) p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => by
      rcases p with ⟨a, i⟩
      fin_cases a
      exact hQ i)
  unfold ev
  conv_lhs => rw [← un1_lift_lemma_2 f]
  rw [MvPowerSeries.subst_comp_subst_apply hA hB]
  congr 1
  funext i
  rw [MvPowerSeries.subst_X hB]
  rfl

theorem fb_add (Y : FBChart C V O dd) (j : Fin dd) :
    MvPowerSeries.subst Y.B.G.F (un1 (Y.lg j)) =
      MvPowerSeries.subst (fun q : Fin dd => (MvPowerSeries.X ((0 : Fin 2), q) : MvPowerSeries (Fin 2 × Fin dd) C))
          (un1 (Y.lg j)) +
        MvPowerSeries.subst (fun q : Fin dd => (MvPowerSeries.X ((1 : Fin 2), q) : MvPowerSeries (Fin 2 × Fin dd) C))
          (un1 (Y.lg j)) := by
  have hpt : ∀ k : Fin 2, ∀ i, MvPowerSeries.constantCoeff (pt C dd k i) = 0 := fun k i => by simp [pt]
  have hadd : ∀ i, MvPowerSeries.constantCoeff (addOf Y.B.G.F (pt C dd 0) (pt C dd 1) i) = 0 := fun i => by
    show MvPowerSeries.constantCoeff (ev (![pt C dd 0, pt C dd 1] : Fin 2 → Pt C 2 dd) (Y.B.G.F i)) = 0
    unfold ev
    rw [cc_subst_lemma _ (fun p => by
      rcases p with ⟨a, k⟩
      fin_cases a <;> simp [pt])]
    exact Y.B.G.const i
  have hF : addOf Y.B.G.F (pt C dd 0) (pt C dd 1) = Y.B.G.F := by
    funext i
    show ev (![pt C dd 0, pt C dd 1] : Fin 2 → Pt C 2 dd) (Y.B.G.F i) = Y.B.G.F i
    have hX : (fun p : Fin 2 × Fin dd => (![pt C dd 0, pt C dd 1] : Fin 2 → Pt C 2 dd) p.1 p.2) =
        MvPowerSeries.X := by
      funext p
      rcases p with ⟨a, k⟩
      fin_cases a <;> rfl
    unfold ev
    rw [hX, ← MvPowerSeries.map_algebraMap_eq_subst_X]
    simp
  have e := Y.lg_add j
  rw [ev1_lemma_3 _ hadd, ev1_lemma_3 _ (hpt 0), ev1_lemma_3 _ (hpt 1), hF] at e
  exact e

variable {d : ℕ} {I0 : Type} [Fintype I0]

theorem lg_self (Y : FBChart C V O dd) (p : SelfData Y d I0) (x : Fin 2 × Fin dd) :
    (Y.rawSelf p).lg x = MvPowerSeries.subst (fun i : Fin dd => (MvPowerSeries.X (x.1, i) : MvPowerSeries (Fin 2 × Fin dd) C))
      (un1 (Y.lg x.2)) := rfl

theorem lgS_add (Y : FBChart C V O dd) (p : SelfData Y d I0) : LgAdd (lawS Y) (Y.rawSelf p).lg := by
  intro k
  have hL : MvPowerSeries.HasSubst (lawS Y) := MvPowerSeries.hasSubst_of_constantCoeff_zero (lawS_const Y)
  have hc : MvPowerSeries.HasSubst
      (fun i : Fin dd => (MvPowerSeries.X (k.1, i) : MvPowerSeries (Fin 2 × Fin dd) C)) := hasSubst_col k.1
  have hτ : MvPowerSeries.HasSubst (fun q : Fin 2 × Fin dd =>
      (MvPowerSeries.X (q.1, (k.1, q.2)) : MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C)) := hasSubst_tau k.1
  have hF : MvPowerSeries.HasSubst Y.B.G.F := MvPowerSeries.hasSubst_of_constantCoeff_zero Y.B.G.const
  have hX0 := MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun q : Fin 2 × Fin dd => (MvPowerSeries.X ((0 : Fin 2), q) : MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C)) (fun _ => by simp)
  have hX1 := MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun q : Fin 2 × Fin dd => (MvPowerSeries.X ((1 : Fin 2), q) : MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C)) (fun _ => by simp)
  have hY0 := MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun q : Fin dd => (MvPowerSeries.X ((0 : Fin 2), q) : MvPowerSeries (Fin 2 × Fin dd) C)) (fun _ => by simp)
  have hY1 := MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun q : Fin dd => (MvPowerSeries.X ((1 : Fin 2), q) : MvPowerSeries (Fin 2 × Fin dd) C)) (fun _ => by simp)
  rw [lg_self Y p k, MvPowerSeries.subst_comp_subst_apply hc hL, MvPowerSeries.subst_comp_subst_apply hc hX0,
    MvPowerSeries.subst_comp_subst_apply hc hX1]
  simp only [MvPowerSeries.subst_X hL, MvPowerSeries.subst_X hX0, MvPowerSeries.subst_X hX1]
  rw [show (fun i : Fin dd => lawS Y (k.1, i)) = fun i => MvPowerSeries.subst (fun q : Fin 2 × Fin dd =>
      (MvPowerSeries.X (q.1, (k.1, q.2)) : MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C)) (Y.B.G.F i) from rfl,
    ← MvPowerSeries.subst_comp_subst_apply hF hτ, fb_add Y k.2, MvPowerSeries.subst_add hτ,
    MvPowerSeries.subst_comp_subst_apply hY0 hτ, MvPowerSeries.subst_comp_subst_apply hY1 hτ]
  simp only [MvPowerSeries.subst_X hτ]

private theorem deg_single_lemma_0 {τ : Type} (c : τ) (n : ℕ) : Finsupp.degree (Finsupp.single c n) = n := by
  first
  | exact Finsupp.degree_single c n

private theorem deg_zero_lemma_0 {τ : Type} (d : τ →₀ ℕ) (h : Finsupp.degree d = 0) : d = 0 := by
  first
  | exact (Finsupp.degree_eq_zero_iff d).mp h

theorem lgS_lin (Y : FBChart C V O dd) (p : SelfData Y d I0) (x : Fin 2 × Fin dd) (μ : Fin 2 × Fin dd →₀ ℕ)
    (hμ : μ.degree ≤ 1) :
    MvPowerSeries.coeff μ ((Y.rawSelf p).lg x) = MvPowerSeries.coeff μ (MvPowerSeries.X x) := by
  apply _root_.Formalism.L2.FormalSeriesBounds.FBChart.rawSelf_lin <;> assumption

theorem exS_lg (Y : FBChart C V O dd) (p : SelfData Y d I0) (x : Fin 2 × Fin dd) :
    MvPowerSeries.subst (Y.rawSelf p).lg ((Y.rawSelf p).ex x) = (MvPowerSeries.X x : MvPowerSeries (Fin 2 × Fin dd) C) := by
  apply _root_.Formalism.L2.FormalSeriesBounds.FBChart.rawSelf_exlg <;> assumption

theorem gm_int (Y : FBChart C V O dd) (p : SelfData Y d I0) (a : ZMod d) (r s : Fin 2) : V.Ge 0 (p.gm a r s) := by
  obtain ⟨M, hM⟩ := p.gm_lim 0
  have h1' := hM a r s
  simp only [Nat.cast_zero] at h1'
  have h1 : (0 : WithTop ℝ) ≤ V.v (p.gm a r s - p.em a (M r s)) := h1'
  have h2 : (0 : WithTop ℝ) ≤ V.v (p.em a (M r s)) := p.em_int a (M r s)
  show (0 : WithTop ℝ) ≤ V.v (p.gm a r s)
  have h3 := le_trans (le_min h1 h2) (AddValuation.map_add V.v _ _)
  rwa [sub_add_cancel] at h3

theorem sat_self (Y : FBChart C V O dd) (p : SelfData Y d I0) (g : Fin 2) :
    ∃ w : Fin 2 × Fin dd → I0 → C, (∀ x c, V.Ge 0 (w x c)) ∧
      ∀ c c' : I0, ∑ x, (Y.rawSelf p).u g c x * w x c' = if c = c' then 1 else 0 := by
  apply _root_.Formalism.L2.FormalSeriesBounds.FBChart.exists_integral_right_inverse <;> assumption

theorem germ_zero_self_conjugate : GermZeroSelfConjugate := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p H
  exact GeneralGermZero.general_germ_zero (Y.rawSelf p) (lawS Y) (fun x => lawS_const Y x) (fun x => lawS_int Y x) (lgS_add Y p)
    (fun x μ hμ => lgS_lin Y p x μ hμ) (fun x => exS_lg Y p x) (sat_self Y p) H

end SelfConjugateGermZero

end Formalism.L2.FormalSeriesBounds
