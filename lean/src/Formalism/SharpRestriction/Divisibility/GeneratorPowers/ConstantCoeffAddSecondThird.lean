import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndFrFix
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.LogLowOrderOne
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThetaSwapFirstTwo
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcAdd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ActLin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ExpLaw
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.HomUniq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.PderivSecondEvFirstPointEqZero

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2b

open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)

variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}

open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing (ev_ev ev_X hasSubst_pts exp_add subst_exp)

theorem cc_logOf (G : FGLaw S d) (i : Fin d) : MvPowerSeries.constantCoeff (LogPf.logOf G i) = 0 := by
  have h0 : ∀ f : PS S 1 d, MvPowerSeries.constantCoeff f = f 0 := fun _ => rfl
  rw [h0]
  simp [LogPf.logOf, LogPf.prim]

theorem cc_pt' {n : ℕ} (j : Fin n) (i : Fin d) : MvPowerSeries.constantCoeff (pt S d j i) = 0 := by
  simp [pt]

theorem ev_eq_hom {m n : ℕ} (a : Fin m → Pt S n d) (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0)
    (f : PS S m d) : ev a f = MvPowerSeries.substAlgHom (hasSubst_pts a ha) f := by
  first
    | rfl
    | (rw [MvPowerSeries.coe_substAlgHom]; rfl)
    | simp [ev, MvPowerSeries.coe_substAlgHom]

theorem ev_at {m n : ℕ} (a : Fin m → Pt S n d) (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (j : Fin m)
    (f : PS S 1 d) : ev a (ev ![pt S d j] f) = ev ![a j] f := by
  have h1 : ∀ (j' : Fin 1) (i : Fin d), MvPowerSeries.constantCoeff ((![pt S d j] : Fin 1 → Pt S m d) j' i) = 0 := by
    intro j' i; fin_cases j'; simp [pt]
  rw [ev_ev _ _ h1 ha]
  congr 1
  funext j' i
  fin_cases j'
  exact ev_X a ha j i

theorem ev_bilL {n : ℕ} (G : FGLaw S d) (cc : Fin d → Fin d → S) (a : Fin 2 → Pt S n d)
    (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) :
    ev a (bilL G cc) = ∑ i, ∑ l, cc i l • (ev ![a 0] (LogPf.logOf G i) * ev ![a 1] (LogPf.logOf G l)) := by
  simp only [bilL, lg]
  rw [ev_eq_hom a ha]
  simp only [map_sum, map_smul, map_mul]
  simp only [← ev_eq_hom a ha]
  simp only [ev_at a ha]

theorem pair_property {A : Type} (P : A → Prop) {u v : Fin d → A}
    (hu : ∀ i, P (u i)) (hv : ∀ i, P (v i)) (j : Fin 2) (i : Fin d) :
    P ((![u, v] : Fin 2 → Fin d → A) j i) := by
  fin_cases j
  · exact hu i
  · exact hv i

/-- The formal logarithm carries addition of zero-constant points to addition of series. -/
theorem formal_log_add_points {n : ℕ} (G : FGLaw S d) (u v : Pt S n d)
    (hu : ∀ i, MvPowerSeries.constantCoeff (u i) = 0)
    (hv : ∀ i, MvPowerSeries.constantCoeff (v i) = 0) (l : Fin d) :
    ev ![G.add u v] (LogPf.logOf G l) =
      ev ![u] (LogPf.logOf G l) + ev ![v] (LogPf.logOf G l) :=
  CIndFrExp2a.formal_log_add_points G u v hu hv l

theorem formal_log_add_last_two (G : FGLaw S d) (l : Fin d) :
    ev (n := 3) ![G.add (pt S d 1) (pt S d 2)] (LogPf.logOf G l) =
      ev (n := 3) ![pt S d 1] (LogPf.logOf G l) + ev (n := 3) ![pt S d 2] (LogPf.logOf G l) := by
  exact formal_log_add_points G _ _ (cc_pt' 1) (cc_pt' 2) l

private theorem cc_ev_lemma {m n : ℕ} (a : Fin m → Pt S n d) (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0)
    (f : PS S m d) (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (ev a f) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_pts a ha) (fun p => ha p.1 p.2) hf

theorem cc_bilL (G : FGLaw S d) (cc : Fin d → Fin d → S) : MvPowerSeries.constantCoeff (bilL G cc) = 0 := by
  have h1 : ∀ (j : Fin 2) (l : Fin d), MvPowerSeries.constantCoeff (lg G j l) = 0 := fun j l =>
    cc_ev_lemma (![pt S d j] : Fin 1 → Pt S 2 d) (fun j' k => by fin_cases j' <;> simp [pt]) _ (cc_logOf G l)
  simp only [bilL]
  rw [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [← smul_mul_assoc, map_mul, h1, mul_zero]

theorem constantCoeff_add_points {n : ℕ} (G : FGLaw S d) (u v : Pt S n d)
    (hu : ∀ i, MvPowerSeries.constantCoeff (u i) = 0)
    (hv : ∀ i, MvPowerSeries.constantCoeff (v i) = 0) (i : Fin d) :
    MvPowerSeries.constantCoeff (G.add u v i) = 0 :=
  cc_ev_lemma ![u, v] (pair_property (fun f => MvPowerSeries.constantCoeff f = 0) hu hv)
    (G.F i) (G.const i)

theorem constantCoeff_add_second_third (G : FGLaw S d) (i : Fin d) : MvPowerSeries.constantCoeff (G.add (pt S (n := 3) d 1) (pt S d 2) i) = 0 := by
  exact constantCoeff_add_points G _ _ (cc_pt' 1) (cc_pt' 2) i

set_option maxHeartbeats 800000 in

theorem ev_expP {n : ℕ} (a : Fin 2 → Pt S n d) (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0)
    (G : FGLaw S d) (cc : Fin d → Fin d → S) :
    ev a (expP (-bilL G cc)) = expP (-ev a (bilL G cc)) := by
  have h0 : MvPowerSeries.constantCoeff (-bilL G cc) = 0 := by
    rw [map_neg, cc_bilL, neg_zero]
  have h1 : ev a (-bilL G cc) = -ev a (bilL G cc) := by
    rw [ev_eq_hom a ha, ev_eq_hom a ha, map_neg]
  rw [← h1]
  have key := subst_exp (k := S) (σ := Fin 2 × Fin d) (τ := Fin n × Fin d) (fun p => a p.1 p.2) (fun p => ha p.1 p.2) h0
  exact key

theorem ev_expP_mul_of_add {n : ℕ} (G : FGLaw S d) (cc : Fin d → Fin d → S)
    (a b c : Fin 2 → Pt S n d)
    (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0)
    (hb : ∀ j i, MvPowerSeries.constantCoeff (b j i) = 0)
    (hc : ∀ j i, MvPowerSeries.constantCoeff (c j i) = 0)
    (hsum : ev a (bilL G cc) = ev b (bilL G cc) + ev c (bilL G cc)) :
    ev a (expP (-bilL G cc)) = ev b (expP (-bilL G cc)) * ev c (expP (-bilL G cc)) := by
  rw [ev_expP _ ha, ev_expP _ hb, ev_expP _ hc, hsum, neg_add]
  exact exp_add (by rw [map_neg, cc_ev_lemma _ hb _ (cc_bilL G cc), neg_zero])
    (by rw [map_neg, cc_ev_lemma _ hc _ (cc_bilL G cc), neg_zero])

theorem twist_mul_first_points {n : ℕ} (G : FGLaw S d) (cc : Fin d → Fin d → S)
    (x y z : Pt S n d)
    (hx : ∀ i, MvPowerSeries.constantCoeff (x i) = 0)
    (hy : ∀ i, MvPowerSeries.constantCoeff (y i) = 0)
    (hz : ∀ i, MvPowerSeries.constantCoeff (z i) = 0) :
    ev ![G.add x y, z] (expP (-bilL G cc)) =
      ev ![x, z] (expP (-bilL G cc)) * ev ![y, z] (expP (-bilL G cc)) := by
  have ha : ∀ j i, MvPowerSeries.constantCoeff ((![G.add x y, z] : Fin 2 → Pt S n d) j i) = 0 :=
    pair_property (fun f : PS S n d => MvPowerSeries.constantCoeff f = 0)
      (u := G.add x y) (v := z) (constantCoeff_add_points G x y hx hy) hz
  have hb : ∀ j i, MvPowerSeries.constantCoeff ((![x, z] : Fin 2 → Pt S n d) j i) = 0 :=
    pair_property (fun f : PS S n d => MvPowerSeries.constantCoeff f = 0)
      (u := x) (v := z) hx hz
  have hc : ∀ j i, MvPowerSeries.constantCoeff ((![y, z] : Fin 2 → Pt S n d) j i) = 0 :=
    pair_property (fun f : PS S n d => MvPowerSeries.constantCoeff f = 0)
      (u := y) (v := z) hy hz
  apply ev_expP_mul_of_add G cc _ _ _ ha hb hc
  rw [ev_bilL G cc _ ha, ev_bilL G cc _ hb, ev_bilL G cc _ hc]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  simp_rw [formal_log_add_points G x y hx hy, add_mul, smul_add, Finset.sum_add_distrib]

theorem twist_mul_second_points {n : ℕ} (G : FGLaw S d) (cc : Fin d → Fin d → S)
    (x y z : Pt S n d)
    (hx : ∀ i, MvPowerSeries.constantCoeff (x i) = 0)
    (hy : ∀ i, MvPowerSeries.constantCoeff (y i) = 0)
    (hz : ∀ i, MvPowerSeries.constantCoeff (z i) = 0) :
    ev ![z, G.add x y] (expP (-bilL G cc)) =
      ev ![z, x] (expP (-bilL G cc)) * ev ![z, y] (expP (-bilL G cc)) := by
  have ha : ∀ j i, MvPowerSeries.constantCoeff ((![z, G.add x y] : Fin 2 → Pt S n d) j i) = 0 :=
    pair_property (fun f : PS S n d => MvPowerSeries.constantCoeff f = 0)
      (u := z) (v := G.add x y) hz (constantCoeff_add_points G x y hx hy)
  have hb : ∀ j i, MvPowerSeries.constantCoeff ((![z, x] : Fin 2 → Pt S n d) j i) = 0 :=
    pair_property (fun f : PS S n d => MvPowerSeries.constantCoeff f = 0)
      (u := z) (v := x) hz hx
  have hc : ∀ j i, MvPowerSeries.constantCoeff ((![z, y] : Fin 2 → Pt S n d) j i) = 0 :=
    pair_property (fun f : PS S n d => MvPowerSeries.constantCoeff f = 0)
      (u := z) (v := y) hz hy
  apply ev_expP_mul_of_add G cc _ _ _ ha hb hc
  rw [ev_bilL G cc _ ha, ev_bilL G cc _ hb, ev_bilL G cc _ hc]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  simp_rw [formal_log_add_points G x y hx hy, mul_add, smul_add, Finset.sum_add_distrib]

theorem twist_mul_second_argument (G : FGLaw S d) (cc : Fin d → Fin d → S) :
    ev (n := 3) ![pt S d 0, G.add (pt S d 1) (pt S d 2)] (expP (-bilL G cc)) =
      ev (n := 3) ![pt S d 0, pt S d 1] (expP (-bilL G cc)) * ev (n := 3) ![pt S d 0, pt S d 2] (expP (-bilL G cc)) := by
  exact twist_mul_second_points G cc _ _ _ (cc_pt' 1) (cc_pt' 2) (cc_pt' 0)

theorem jetSubstP_psJet {n n' : ℕ} (m : ℕ) (φ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S) (a : Fin n → Pt S n' d)
    (ha : ∀ p : Fin n × Fin d, MvPowerSeries.constantCoeff (a p.1 p.2) = 0)
    (hφ : ∀ p, constantCoeff (φ p) = 0)
    (hmk : ∀ p : Fin n × Fin d, Ideal.Quotient.mk (Formalism.L2.Pj.orig S (Fin n' × Fin d) ^ (m + 1)) (φ p) = psJet m (a p.1 p.2))
    (f : PS S n d) : jetSubstP m φ (psJet m f) = psJet m (ev a f) := by
  rw [ev, FBIdJet.psJet_subst m _ ha f]
  apply DFunLike.congr_fun
  refine GermD.jet_hom_ext fun p => ?_
  rw [GermD.jetMap_mk, aeval_X]
  simp only [jetSubstP, GermD.jetMap_mk, aeval_X, hφ p, map_zero, sub_zero]
  rw [hmk p]
  rfl

theorem mk_X_psJet {n : ℕ} (m : ℕ) (q : Fin n × Fin d) :
    Ideal.Quotient.mk (Formalism.L2.Pj.orig S (Fin n × Fin d) ^ (m + 1)) (X q) = psJet m (pt S d q.1 q.2) := by
  unfold psJet
  rw [Ideal.Quotient.eq]
  have hc : ∀ e, MvPowerSeries.coeff e (pt S d q.1 q.2) = if e = Finsupp.single q 1 then (1 : S) else 0 := by
    intro e; simp [pt, MvPowerSeries.coeff_X]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [zero_add, pow_one]
    refine sub_mem (Ideal.subset_span ⟨q, rfl⟩) ?_
    unfold psTrunc
    refine Ideal.sum_mem _ fun e _ => ?_
    rw [hc]
    split_ifs with he
    · subst he
      exact Ideal.subset_span ⟨q, rfl⟩
    · rw [map_zero]
      exact Ideal.zero_mem _
  · have hmem : Finsupp.single q 1 ∈ degLE m := by
      unfold degLE
      rw [Finset.mem_filter, Finset.mem_image]
      refine ⟨⟨fun i => if i = q then ⟨1, by omega⟩ else 0, Finset.mem_univ _, ?_⟩, ?_⟩
      · ext i
        by_cases h : i = q
        · subst h
          simp
        · simp [h, Finsupp.single_apply, Ne.symm h]
      · rw [Finsupp.sum_single_index rfl]
        show 1 ≤ m
        omega
    have ht : psTrunc m (pt S d q.1 q.2) = X q := by
      unfold psTrunc
      rw [Finset.sum_eq_single (Finsupp.single q 1)]
      · rw [hc, if_pos rfl]
        rfl
      · intro b _ hb
        rw [hc, if_neg hb, map_zero]
      · intro h
        exact absurd hmem h
    rw [ht, sub_self]
    exact Ideal.zero_mem _

theorem mk_psIn_psJet {n n' : ℕ} (m : ℕ) (σ : Fin n → Fin n') (f : PS S n d) :
    Ideal.Quotient.mk (Formalism.L2.Pj.orig S (Fin n' × Fin d) ^ (m + 1)) (psIn d m σ f) =
      psJet m (ev (fun i => pt S d (σ i)) f) := by
  have ha : ∀ p : Fin n × Fin d, MvPowerSeries.constantCoeff ((fun i => pt S d (σ i)) p.1 p.2) = 0 := fun p => cc_pt' _ _
  have hφ : ∀ p : Fin n × Fin d, MvPolynomial.constantCoeff (X (σ p.1, p.2) : MvPolynomial (Fin n' × Fin d) S) = 0 :=
    fun p => by simp
  have hmk : ∀ p : Fin n × Fin d, Ideal.Quotient.mk (Formalism.L2.Pj.orig S (Fin n' × Fin d) ^ (m + 1)) (X (σ p.1, p.2)) =
      psJet m ((fun i => pt S d (σ i)) p.1 p.2) := fun p => mk_X_psJet m (σ p.1, p.2)
  rw [← jetSubstP_psJet m (fun p : Fin n × Fin d => (X (σ p.1, p.2) : MvPolynomial (Fin n' × Fin d) S)) (fun i => pt S d (σ i)) ha hφ hmk f]
  unfold jetSubstP jetMap liftJet psJet psIn
  simp only [MvPolynomial.constantCoeff_X, map_zero, sub_zero, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk,
    AlgHom.coe_toRingHom, AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  have hr : (aeval fun i : Fin n × Fin d => (X (σ i.1, i.2) : MvPolynomial (Fin n' × Fin d) S)) =
      rename (fun p : Fin n × Fin d => (σ p.1, p.2)) :=
    MvPolynomial.algHom_ext fun i => by simp
  erw [Ideal.Quotient.lift_mk]
  simp only [AlgHom.coe_toRingHom, AlgHom.comp_apply, hr, Ideal.Quotient.mkₐ_eq_mk]

/-- A coordinatewise polynomial representative of a point in the truncated series ring. -/
def RepresentsPointJet {n : ℕ} (m : ℕ)
    (φ : Fin d → MvPolynomial (Fin n × Fin d) S) (u : Pt S n d) : Prop :=
  ∀ i, constantCoeff (φ i) = 0 ∧ MvPowerSeries.constantCoeff (u i) = 0 ∧
    Ideal.Quotient.mk (orig S (Fin n × Fin d) ^ (m + 1)) (φ i) = psJet m (u i)

theorem standard_point_jet {n : ℕ} (m : ℕ) (k : Fin n) :
    RepresentsPointJet m (fun i => X (k, i)) (pt S d k) :=
  fun i => ⟨constantCoeff_X S _, cc_pt' k i, mk_X_psJet m (k, i)⟩

theorem psIn_point_jet {n n' : ℕ} (m : ℕ) (σ : Fin n → Fin n') (u : Pt S n d)
    (hu : ∀ i, MvPowerSeries.constantCoeff (u i) = 0) :
    RepresentsPointJet m (fun i => psIn d m σ (u i)) (fun i => ev (fun j => pt S d (σ j)) (u i)) := by
  intro i
  refine ⟨?_, cc_ev_lemma _ (fun j k => cc_pt' (σ j) k) _ (hu i), mk_psIn_psJet m σ (u i)⟩
  rw [FBIdPh.cc_psIn, hu]

theorem add_point_jet {n : ℕ} (G : FGLaw S d) (m : ℕ) (k l : Fin n) :
    RepresentsPointJet m (fun i => psIn d m ![k, l] (G.F i)) (G.add (pt S d k) (pt S d l)) := by
  have hpoints : (fun i => pt S d ((![k, l] : Fin 2 → Fin n) i)) = ![pt S d k, pt S d l] := by
    funext i
    fin_cases i <;> rfl
  have h := psIn_point_jet m (![k, l] : Fin 2 → Fin n) G.F G.const
  rw [hpoints] at h
  exact h

theorem comp_point_jet {n : ℕ} (m : ℕ) (k : Fin n) (u : Pt S 1 d)
    (hu : ∀ i, MvPowerSeries.constantCoeff (u i) = 0) :
    RepresentsPointJet m (fun i => psIn d m ![k] (u i)) (comp1 u (pt S d k)) := by
  have hpoints : (fun i => pt S d ((![k] : Fin 1 → Fin n) i)) = ![pt S d k] := by
    funext i
    fin_cases i
    rfl
  have h := psIn_point_jet m (![k] : Fin 1 → Fin n) u hu
  rw [hpoints] at h
  exact h

theorem jetSubstP_pair {n : ℕ} (m : ℕ)
    {φ ψ : Fin d → MvPolynomial (Fin n × Fin d) S} {u v : Pt S n d}
    (hu : RepresentsPointJet m φ u) (hv : RepresentsPointJet m ψ v) (f : PS S 2 d) :
    jetSubstP m (fun p : Fin 2 × Fin d =>
      (![φ, ψ] : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S) p.1 p.2) (psJet m f) =
      psJet m (ev ![u, v] f) := by
  apply jetSubstP_psJet
  · exact fun p => pair_property (fun f : PS S n d => MvPowerSeries.constantCoeff f = 0)
      (fun i => (hu i).2.1) (fun i => (hv i).2.1) p.1 p.2
  · exact fun p => pair_property (fun f : MvPolynomial (Fin n × Fin d) S => constantCoeff f = 0)
      (fun i => (hu i).1) (fun i => (hv i).1) p.1 p.2
  · rintro ⟨k, i⟩
    fin_cases k
    · exact (hu i).2.2
    · exact (hv i).2.2

theorem twist_mul_second_argument_jet (G : FGLaw S d) (cc : Fin d → Fin d → S) (m : ℕ) :
    jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (G.F j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) (psJet m (expP (-bilL G cc))) =
      jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) (psJet m (expP (-bilL G cc))) *
      jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) (psJet m (expP (-bilL G cc))) := by
  have hX (k : Fin 3) := standard_point_jet (S := S) (d := d) m k
  rw [jetSubstP_pair m (hX 0) (add_point_jet G m 1 2),
    jetSubstP_pair m (hX 0) (hX 1), jetSubstP_pair m (hX 0) (hX 2),
    twist_mul_second_argument, FBIdJet.psJet_mul]

theorem bal_sum {R : Type} [CommRing R] [Algebra S R] (cc M N : Matrix (Fin d) (Fin d) S)
    (hbal : Matrix.transpose M * cc = cc * N) (u v : Fin d → R) :
    ∑ i, ∑ l, cc i l • ((∑ k, M i k • u k) * v l) = ∑ i, ∑ l, cc i l • (u i * ∑ k, N l k • v k) := by
  have key : ∀ a b, ∑ i, cc i b * M i a = ∑ l, cc a l * N l b := by
    intro a b
    have h := congrFun (congrFun hbal a) b
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hL : ∑ i, ∑ l, cc i l • ((∑ k, M i k • u k) * v l) =
      ∑ a, ∑ b, (∑ i, cc i b * M i a) • (u a * v b) := by
    simp only [Finset.sum_mul, Finset.smul_sum, Finset.sum_smul, smul_mul_assoc, smul_smul]
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    exact Finset.sum_comm
  have hR : ∑ i, ∑ l, cc i l • (u i * ∑ k, N l k • v k) =
      ∑ a, ∑ b, (∑ l, cc a l * N l b) • (u a * v b) := by
    simp only [Finset.mul_sum, Finset.smul_sum, Finset.sum_smul, mul_smul_comm, smul_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_comm
  rw [hL, hR]
  simp only [key]

abbrev lgv (G : FGLaw S d) : Pt S 1 d := fun i => LogPf.logOf G i

theorem dLin_lgv (G : FGLaw S d) : dLin (lgv G) = 1 := by
  refine Matrix.ext fun i j => ?_
  show MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (LogPf.logOf G i) = (1 : Matrix (Fin d) (Fin d) S) i j
  have h := congrArg MvPowerSeries.constantCoeff (LogPf.pderiv_logOf G i j)
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv, zero_add] at h
  have h2 := congrFun (congrFun (LogPf.cc_om G) i) j
  simp only [Matrix.map_apply] at h2
  simpa [h2] using h

private theorem ev_id_lemma_2 (G : FGLaw S d) (i : Fin d) : ev (n := 2) ![pt S d 0, pt S d 1] (G.F i) = G.F i := by
  have h01 : ∀ (j : Fin 2) (k : Fin d), MvPowerSeries.constantCoeff ((![pt S d 0, pt S d 1] : Fin 2 → Pt S 2 d) j k) = 0 := by
    intro j k; fin_cases j <;> simp [pt]
  have h10 : ∀ (j : Fin 2) (k : Fin d), MvPowerSeries.constantCoeff ((![pt S d 1, pt S d 0] : Fin 2 → Pt S 2 d) j k) = 0 := by
    intro j k; fin_cases j <;> simp [pt]
  conv_lhs => rw [← G.comm i]
  rw [ev_ev _ _ h10 h01]
  refine Eq.trans ?_ (G.comm i)
  congr 1
  funext j k
  fin_cases j
  · exact ev_X _ h01 1 k
  · exact ev_X _ h01 0 k

theorem add_lgv (G : FGLaw S d) :
    comp1 (lgv G) (G.add (pt S (n := 2) d 0) (pt S (n := 2) d 1)) =
      comp1 (lgv G) (pt S (n := 2) d 0) + comp1 (lgv G) (pt S (n := 2) d 1) := by
  funext i
  have e : G.add (pt S (n := 2) d 0) (pt S (n := 2) d 1) = G.F := by
    funext j; exact ev_id_lemma_2 G j
  rw [e]
  exact LogPf.logOf_add (G := G) i

theorem ev_lin {n : ℕ} (M : Matrix (Fin d) (Fin d) S) (u : Pt S n d) (hu : ∀ i, MvPowerSeries.constantCoeff (u i) = 0)
    (i : Fin d) :
    ev ![u] (∑ j, MvPowerSeries.C (M i j) * (MvPowerSeries.X ((0 : Fin 1), j) : PS S 1 d)) = ∑ j, M i j • u j := by
  have hu' : ∀ (j : Fin 1) (k : Fin d), MvPowerSeries.constantCoeff ((![u] : Fin 1 → Pt S n d) j k) = 0 := by
    intro j k; fin_cases j; simpa using hu k
  rw [ev_eq_hom _ hu', map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← MvPowerSeries.smul_eq_C_mul, map_smul, ← ev_eq_hom _ hu', ev_X _ hu']
  rfl

theorem log_act {O : Type} [CommRing O] [StarRing O] (B : FB S d O) (a : O) (i : Fin d) :
    comp1 (lgv B.G) (B.A.act a) i = ∑ j, dLin (B.A.act a) i j • lgv B.G j := by
  obtain ⟨ε, hinv, -⟩ := WickVanishing.formal_exp_law S d B.G (lgv B.G) (cc_logOf B.G) (dLin_lgv B.G) (add_lgv B.G)
  have hlin := WickVanishing.action_linear S d O B (lgv B.G) ε (cc_logOf B.G) (dLin_lgv B.G) (add_lgv B.G) hinv a
  have hε0 : ∀ i, MvPowerSeries.constantCoeff (ε i) = 0 := hinv.1
  have hl0 : ∀ i, MvPowerSeries.constantCoeff (lgv B.G i) = 0 := cc_logOf B.G
  have hA0 : ∀ i, MvPowerSeries.constantCoeff (B.A.act a i) = 0 := B.A.const a
  have hAε : ∀ i, MvPowerSeries.constantCoeff (comp1 (B.A.act a) ε i) = 0 := WickVanishing.cc_comp1 _ _ hA0 hε0
  have e1 : comp1 (lgv B.G) (B.A.act a) = comp1 (comp1 (lgv B.G) (comp1 (B.A.act a) ε)) (lgv B.G) := by
    conv_lhs => rw [← WickVanishing.composition_identity_point_right (B.A.act a), ← hinv.2.2.1]
    rw [WickVanishing.germComp1_germComp1_eq_substitute _ _ _ hε0 hl0, WickVanishing.germComp1_germComp1_eq_substitute _ _ _ hAε hl0]
  rw [e1]
  show ev ![lgv B.G] (comp1 (lgv B.G) (comp1 (B.A.act a) ε) i) = _
  rw [hlin i, ev_lin _ _ hl0]

theorem ev_act_pt {O : Type} [CommRing O] [StarRing O] (B : FB S d O) (a : O) {n : ℕ} (q : Fin n) (i : Fin d) :
    ev ![comp1 (B.A.act a) (pt S d q)] (LogPf.logOf B.G i) =
      ∑ j, dLin (B.A.act a) i j • ev ![pt S d q] (LogPf.logOf B.G j) := by
  have hq : ∀ (j : Fin 1) (k : Fin d), MvPowerSeries.constantCoeff ((![pt S d q] : Fin 1 → Pt S n d) j k) = 0 := by
    intro j k; fin_cases j; simp [pt]
  have hA : ∀ (j : Fin 1) (k : Fin d), MvPowerSeries.constantCoeff ((![B.A.act a] : Fin 1 → Pt S 1 d) j k) = 0 := by
    intro j k; fin_cases j; simpa using B.A.const a k
  have e := ev_ev (![B.A.act a] : Fin 1 → Pt S 1 d) (![pt S d q] : Fin 1 → Pt S n d) hA hq (LogPf.logOf B.G i)
  have h2 : ev (![B.A.act a] : Fin 1 → Pt S 1 d) (LogPf.logOf B.G i) = ∑ j, dLin (B.A.act a) i j • lgv B.G j :=
    log_act B a i
  refine Eq.trans ?_ (e.symm.trans ?_)
  · congr 1
    funext j k
    fin_cases j
    rfl
  · rw [h2, ev_eq_hom _ hq, map_sum]
    simp only [map_smul]
    simp only [← ev_eq_hom _ hq]

theorem twist_bal {O : Type} [CommRing O] [StarRing O] (B : FB S d O) (cc : Fin d → Fin d → S) (a b : O)
    (hbal : Matrix.transpose (dLin (B.A.act a)) * Matrix.of cc = Matrix.of cc * dLin (B.A.act b)) :
    ev (n := 2) ![comp1 (B.A.act a) (pt S d 0), pt S d 1] (expP (-bilL B.G cc)) =
      ev (n := 2) ![pt S d 0, comp1 (B.A.act b) (pt S d 1)] (expP (-bilL B.G cc)) := by
  have cA : ∀ (k : Fin d), MvPowerSeries.constantCoeff (comp1 (B.A.act a) (pt S (n := 2) d 0) k) = 0 := fun k =>
    cc_ev_lemma (![pt S d 0] : Fin 1 → Pt S 2 d) (fun j k' => by fin_cases j <;> simp [pt]) _ (B.A.const a k)
  have cB : ∀ (k : Fin d), MvPowerSeries.constantCoeff (comp1 (B.A.act b) (pt S (n := 2) d 1) k) = 0 := fun k =>
    cc_ev_lemma (![pt S d 1] : Fin 1 → Pt S 2 d) (fun j k' => by fin_cases j <;> simp [pt]) _ (B.A.const b k)
  have h0 : ∀ (j : Fin 2) (k : Fin d), MvPowerSeries.constantCoeff ((![comp1 (B.A.act a) (pt S d 0), pt S d 1] : Fin 2 → Pt S 2 d) j k) = 0 := by
    intro j k; fin_cases j
    · simpa using cA k
    · simp [pt]
  have h1 : ∀ (j : Fin 2) (k : Fin d), MvPowerSeries.constantCoeff ((![pt S d 0, comp1 (B.A.act b) (pt S d 1)] : Fin 2 → Pt S 2 d) j k) = 0 := by
    intro j k; fin_cases j
    · simp [pt]
    · simpa using cB k
  have key := bal_sum (R := PS S 2 d) (Matrix.of cc) (dLin (B.A.act a)) (dLin (B.A.act b)) hbal
    (fun k => ev (n := 2) ![pt S d 0] (LogPf.logOf B.G k)) (fun l => ev (n := 2) ![pt S d 1] (LogPf.logOf B.G l))
  simp only [Matrix.of_apply] at key
  rw [ev_expP _ h0, ev_expP _ h1, ev_bilL _ _ _ h0, ev_bilL _ _ _ h1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, ev_act_pt]
  rw [key]

theorem twist_bal_jet {O : Type} [CommRing O] [StarRing O] (B : FB S d O) (cc : Fin d → Fin d → S) (a b : O)
    (hbal : Matrix.transpose (dLin (B.A.act a)) * Matrix.of cc = Matrix.of cc * dLin (B.A.act b)) (m : ℕ) :
    jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => psIn d m ![0] (B.A.act a j), fun j => X ((1 : Fin 2), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) (psJet m (expP (-bilL B.G cc))) =
      jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (B.A.act b j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) (psJet m (expP (-bilL B.G cc))) := by
  have hX (k : Fin 2) := standard_point_jet (S := S) (d := d) m k
  rw [jetSubstP_pair m (comp_point_jet m 0 (B.A.act a) (B.A.const a)) (hX 1),
    jetSubstP_pair m (hX 0) (comp_point_jet m 1 (B.A.act b) (B.A.const b)),
    twist_bal B cc a b hbal]

end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2b
