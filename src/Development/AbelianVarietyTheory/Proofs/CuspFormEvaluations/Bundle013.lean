module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsMemRowHighestTotalDegreeEqTwo
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.L2NormFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ContinuousThetaSectionPointwiseNormSq
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsBasisSpanEqOfCommensurable
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle010
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle011
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle007
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.TraceHermNondegenerate
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.MvPolynomial.Funext
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm

@[expose] public section

section

open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo

namespace GlobalTheory.Harm

section General

theorem isWeightedHomogeneous_rename_iff {R σ τ M : Type*} [CommSemiring R] [AddCommMonoid M]
    {f : σ → τ} (hf : Function.Injective f) (w : τ → M) (P : MvPolynomial σ R) (d : M) :
    IsWeightedHomogeneous w (rename f P) d ↔ IsWeightedHomogeneous (w ∘ f) P d := by
  classical
  have hw (m : σ →₀ ℕ) : Finsupp.weight w (m.mapDomain f) = Finsupp.weight (w ∘ f) m := by
    simp only [Finsupp.weight_apply]
    rw [Finsupp.sum_mapDomain_index (by simp) (by simp [add_smul])]
    rfl
  constructor
  · intro h m hm
    rw [← hw]
    exact h (by rwa [coeff_rename_mapDomain f hf])
  · intro h m hm
    obtain ⟨u, rfl, hu⟩ := coeff_rename_ne_zero f P m hm
    rw [hw, h hu]

variable {T κ : Type*} [Fintype κ] {p q : ℕ}

theorem rowDegree_le_of_rowAdd_eq {R : Type*} [CommRing R] [IsDomain R] [CharZero R] {t : T}
    {r r' : Fin p ⊕ Fin q} (hr : r ≠ r') {P : Poly R T p q κ} (hP : P ≠ 0) {d d' : ℕ}
    (hd : IsWeightedHomogeneous (rowInd t r) P d) (hd' : IsWeightedHomogeneous (rowInd t r') P d')
    (h : ∀ s : ℤ, rowAdd t r r' (s : R) P = P) : d' ≤ d := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  let K := FractionRing R
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  haveI : CharZero K := charZero_of_injective_algebraMap hinj
  have hinv (s : K) : rowAdd t r r' s (map (algebraMap R K) P) = map (algebraMap R K) P :=
    rowAdd_eq_self_of_forall_int (fun s => by
      rw [← map_intCast (algebraMap R K), ← map_rowAdd, h]) s
  have hmap {w : Var T p q κ → ℕ} {e : ℕ} (he : IsWeightedHomogeneous w P e) :
      IsWeightedHomogeneous w (map (algebraMap R K) P) e := fun m hm =>
    he fun e => hm (by rw [coeff_map, e, map_zero])
  have hQ : map (algebraMap R K) P ≠ 0 := fun e => hP (map_injective _ hinj (by rw [e, map_zero]))
  replace hd := hmap hd
  replace hd' := hmap hd'
  generalize map (algebraMap R K) P = Q at hinv hQ hd hd'
  refine hQ (MvPolynomial.funext fun z => ?_)
  let f : Var T p q κ → Polynomial K := fun v => Polynomial.C (z v) +
    if v.1 = t ∧ v.2.1 = r then Polynomial.C (z (t, r', v.2.2)) * Polynomial.X else 0
  let g : Var T p q κ → Polynomial K := fun v =>
    if v.1 = t ∧ v.2.1 = r' then Polynomial.C (z (t, r, v.2.2)) else f v
  have hev (u : Var T p q κ → Polynomial K) (s : K) :
      (aeval u Q).eval s = eval (fun v => (u v).eval s) Q := by
    rw [← Polynomial.coe_aeval_eq_eval, ← coe_aeval_eq_eval]
    change Polynomial.aeval s (aeval u Q) = aeval _ Q
    rw [comp_aeval_apply]
  have hscale (c : K) (x : Var T p q κ → K) :
      eval (fun v => c ^ rowInd t r' v * x v) Q = c ^ d' * eval x Q := by
    rw [eval_eq, eval_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [← hd' (mem_support_iff.1 hm), Finsupp.weight_apply, Finsupp.sum]
    simp only [mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum,
      smul_eq_mul, mul_comm (m _)]
    ring
  have hid : Polynomial.X ^ d' * aeval f Q = Polynomial.C ((-1) ^ d') * aeval g Q := by
    refine Polynomial.eq_of_infinite_eval_eq _ _
      (((Set.finite_singleton (0 : K)).infinite_compl).mono fun s hs => ?_)
    have hs : s ≠ 0 := hs
    have h1 : eval (fun v => (f v).eval s) Q = (-s⁻¹) ^ d' * eval (fun v => (g v).eval s) Q := by
      rw [← hscale]
      conv_lhs => rw [← hinv (-s⁻¹), eval_rowAdd]
      congr 2
      funext ⟨t', r'', k⟩
      rw [rowInd_apply]
      by_cases e : t' = t ∧ r'' = r'
      · obtain ⟨rfl, rfl⟩ := e
        simp only [f, g, hr.symm, and_self, and_false, if_true, if_false, Polynomial.eval_add,
          Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, add_zero, pow_one]
        linear_combination (-z (t', r'', k)) * mul_inv_cancel₀ hs
      · simp [g, e]
    rw [Set.mem_setOf_eq, Polynomial.eval_mul, Polynomial.eval_mul, hev, hev, h1,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, ← mul_assoc, ← mul_pow,
      mul_neg, mul_inv_cancel₀ hs]
  have hg (v : Var T p q κ) : (g v).natDegree ≤ rowInd t r v := by
    rw [rowInd_apply]
    simp only [g, f]
    split_ifs
    · simp
    · simp
    · compute_degree
    · simp
  have hdeg : (aeval g Q).natDegree ≤ d := by
    rw [aeval_def, eval₂_eq]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
    rw [← hd (mem_support_iff.1 hm), Finsupp.weight_apply, Finsupp.sum]
    refine (Polynomial.natDegree_C_mul_le _ _).trans ((Polynomial.natDegree_prod_le _ _).trans
      (Finset.sum_le_sum fun v _ => Polynomial.natDegree_pow_le.trans ?_))
    exact Nat.mul_le_mul_left _ (hg v)
  have := congrArg (fun F : Polynomial K => F.coeff d') hid
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hlt),
    mul_zero] at this
  rw [Polynomial.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    Polynomial.coeff_zero_eq_eval_zero, hev] at this
  rw [map_zero, ← this]
  congr 2
  funext v
  simp [f]
  split_ifs <;> simp

end General

section Rows

variable {ι : Type*} {σ : ι → ι} {Ψ : ι → Prop} {dim : ι → ℕ} {p q : ℕ}


open scoped Classical in
open Classical in
noncomputable def halfRowEquiv (hσ : Function.Involutive σ) (hΨ : ∀ τ, ¬ Ψ τ ↔ Ψ (σ τ))
    (hp : ∀ τ, Ψ τ → dim τ = p) (hq : ∀ τ, Ψ τ → dim (σ τ) = q) :
    (Σ τ : ι, Fin (dim τ)) ≃ {τ // Ψ τ} × (Fin p ⊕ Fin q) where
  toFun x := if h : Ψ x.1 then (⟨x.1, h⟩, Sum.inl (x.2.cast (hp _ h)))
    else (⟨σ x.1, (hΨ _).1 h⟩,
      Sum.inr (x.2.cast ((congrArg dim (hσ x.1)).symm.trans (hq _ ((hΨ _).1 h)))))
  invFun y := y.2.elim (fun a => ⟨y.1.1, a.cast (hp _ y.1.2).symm⟩)
    fun b => ⟨σ y.1.1, b.cast (hq _ y.1.2).symm⟩
  left_inv x := by
    by_cases h : Ψ x.1
    · beta_reduce; rw [dif_pos h]; rfl
    · beta_reduce; rw [dif_neg h]
      exact Sigma.ext (hσ _) ((Fin.heq_ext_iff (congrArg dim (hσ _))).2 rfl)
  right_inv := by
    rintro ⟨⟨τ, h⟩, a | b⟩
    · exact dif_pos h
    · have h' : ¬ Ψ (σ τ) := fun e => (hΨ τ).2 e h
      exact (dif_neg h').trans (Prod.ext (Subtype.ext (hσ τ)) rfl)

end Rows

section Coord

variable {E : Type} [Field E] {Ψ : (E →+* ℂ) → Prop} {dim : (E →+* ℂ) → ℕ}
  {p q : ℕ} (n : ℕ) (hΨ : ∀ τ, ¬ Ψ τ ↔ Ψ (ComplexEmbedding.conjugate τ))
  (hp : ∀ τ, Ψ τ → dim τ = p) (hq : ∀ τ, Ψ τ → dim (ComplexEmbedding.conjugate τ) = q)

end Coord

section Host

variable {E : Type} [Field E] [NumberField E] [IsCMField E]



omit [NumberField E] [IsCMField E] in
@[simp] theorem conjEmb_conjEmb (τ : E →+* ℂ) : Tor.conjEmb (Tor.conjEmb τ) = τ :=
  ComplexEmbedding.involutive_conjugate E τ

variable (H : Tor.Host E)

theorem emb_rt_sq (τ : E →+* ℂ) : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
  have := congrArg (fun a : 𝓞 E => τ (a : E)) H.rt_sq
  simpa using this

theorem conjEmb_rt (τ : E →+* ℂ) : Tor.conjEmb τ (H.rt : E) = -τ (H.rt : E) := by
  first
  | exact @_root_.GlobalTheory.ConjugateEmbeddingSquareRoot.conjEmb_rt
  | exact _root_.GlobalTheory.ConjugateEmbeddingSquareRoot.conjEmb_rt
  | (apply _root_.GlobalTheory.ConjugateEmbeddingSquareRoot.conjEmb_rt <;> assumption)
  | (intros; apply _root_.GlobalTheory.ConjugateEmbeddingSquareRoot.conjEmb_rt <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ConjugateEmbeddingSquareRoot.conjEmb_rt <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ConjugateEmbeddingSquareRoot.conjEmb_rt ..)

theorem not_mem_hostType_iff (τ : E →+* ℂ) :
    ¬ τ (H.rt : E) = H.rt0 ↔ Tor.conjEmb τ (H.rt : E) = H.rt0 := by
  rw [conjEmb_rt]
  have h := (emb_rt_sq H τ).trans H.sqrt_neg_disc_sq.symm
  constructor
  · intro hne
    rw [(sq_eq_sq_iff_eq_or_eq_neg.1 h).resolve_left hne, neg_neg]
  · intro h1 h2
    have h0 : H.rt0 = 0 := by linear_combination (-1 / 2 : ℂ) * (h1 + h2)
    have := H.sqrt_neg_disc_sq
    rw [h0, zero_pow two_ne_zero, eq_comm, neg_eq_zero, Nat.cast_eq_zero] at this
    exact H.d_prime.ne_zero this

variable {H} (D : Tor.Datum H)

theorem mult_of_mem {τ : E →+* ℂ} (h : τ (H.rt : E) = H.rt0) : D.mult τ = D.p := if_pos h

theorem mult_conjEmb_of_mem {τ : E →+* ℂ} (h : τ (H.rt : E) = H.rt0) :
    D.mult (Tor.conjEmb τ) = D.q := if_neg fun e => (not_mem_hostType_iff H τ).2 e h

variable (n : ℕ)

variable {D n}

end Host

end GlobalTheory.Harm
end

section

namespace GlobalTheory.TensorLat

open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem isogeny_sum_tensorLat (T : PT E) (w₀ : 𝓞 E) (hw : (w₀ : E) + cc (w₀ : E) = 1)
    (heps : ∀ x ∈ T.L, (T.eps x : ℝ) = Real.cos (Real.pi * (Hf x (act w₀ x)).im))
    (Λ' : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ')
    (R : Finset (Fin n → Vsp T.dim)) (hR : ∀ y ∈ R, y ∈ tensorLat T Λ')
    (hR' : ∀ y ∈ tensorLat T Λ', ∃! r, r ∈ R ∧ ∀ k, y k - r k ∈ T.L)
    (F : (Fin n → Vsp T.dim) → ℂ) (hF : F ∈ T.Sec 1 n)
    (Y' : GT (Fin n × Idx T.dim)) (hY' : ∀ γ, flat γ ∈ lat Y'.b ↔ γ ∈ tensorLat T Λ')
    (hka' : ∀ γ, Y'.ka (flat γ) = tensorEps w₀ γ) :
    (∑ y ∈ R, tensorEps w₀ y • T.U 1 y F) ∘ flat.symm ∈ Y'.Sec 1 ∧
      Y'.l2 1 ((∑ y ∈ R, tensorEps w₀ y • T.U 1 y F) ∘ flat.symm) = R.card * T.l2 1 F := by
  classical
  obtain ⟨⟨Y, hY, hka⟩, h2, h3, h4⟩ := principal_torus_of_selfDual T (stdLat E n) stdLat_fg
    (fun _ hx => mem_stdLat_iff_herm.1 hx) (fun _ hx => mem_stdLat_iff_herm.2 hx) w₀ hw
  obtain ⟨-, h2', -, -⟩ := principal_torus_of_selfDual T Λ' hfg hint hdual w₀ hw
  obtain ⟨hFm, hFl⟩ := (h3 heps Y hY hka).2 F hF
  set U : ℕ → EuclideanSpace ℂ (Fin n × Idx T.dim) → (EuclideanSpace ℂ (Fin n × Idx T.dim) → ℂ) →
      EuclideanSpace ℂ (Fin n × Idx T.dim) → ℂ := fun q a G v =>
    cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * G (v - a) with hUdef
  have hU : ∀ (q : ℕ) a G v,
      U q a G v = cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * G (v - a) :=
    fun _ _ _ _ => rfl
  let e : (Fin n → Vsp T.dim) ↪ EuclideanSpace ℂ (Fin n × Idx T.dim) :=
    ⟨flat, (flat (n := n) (ι := Idx T.dim)).injective⟩
  have he : ∀ y, e y = flat y := fun _ => rfl
  have key := isogeny_sum_mem_and_norm U hU Y Y' (h2 Y hY hka).2 (h2' Y' hY' hka').2
    (fun x _ _ => by
      obtain ⟨γ, rfl⟩ := (flat (n := n) (ι := Idx T.dim)).surjective x
      rw [hka, hka'])
    (R.map e)
    (fun y hy => by
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_map.1 hy
      exact (hY' γ).2 (hR γ hγ))
    (fun y hy => by
      obtain ⟨γ, rfl⟩ := (flat (n := n) (ι := Idx T.dim)).surjective y
      obtain ⟨r, ⟨hr, hr'⟩, hu⟩ := hR' γ ((hY' γ).1 hy)
      refine ⟨flat r, ⟨Finset.mem_map.2 ⟨r, hr, rfl⟩, ?_⟩, ?_⟩
      · rw [← map_sub, hY, mem_tensorLat_stdLat]
        exact hr'
      · rintro z ⟨hz, hz'⟩
        obtain ⟨r', hr2, rfl⟩ := Finset.mem_map.1 hz
        rw [he, ← map_sub, hY, mem_tensorLat_stdLat] at hz'
        rw [he, hu r' ⟨hr2, hz'⟩])
    (F ∘ flat.symm) hFm
  have e1 : (∑ y ∈ R.map e, Y'.ka y • U 1 y (F ∘ flat.symm)) =
      (∑ y ∈ R, tensorEps w₀ y • T.U 1 y F) ∘ flat.symm := by
    rw [Finset.sum_map]
    funext v
    simp only [he, hka', h4 U hU, Finset.sum_apply, Function.comp_apply, Pi.smul_apply]
  rw [e1, Finset.card_map, hFl] at key
  exact key

theorem exists_min_period (T : PT E) (Λ' : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ')
    {lam : ℝ} (hlam : 0 < lam) (hmin : ∀ x ∈ T.L, x ≠ 0 → lam ≤ ‖x‖) :
    ∃ lam' : ℝ, 0 < lam' ∧ (∀ γ ∈ tensorLat T Λ', γ ≠ 0 → lam' ≤ ‖flat γ‖) ∧
      (1 + 4 * Real.sqrt (2 * Fintype.card (Fin n × Idx T.dim)) / (Real.sqrt Real.pi * lam')) ^
          Fintype.card (Fin n × Idx T.dim) =
        (1 + 4 * Real.sqrt (2 * Fintype.card (Idx T.dim) * n) *
          (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) / (Real.sqrt Real.pi * lam)) ^
          (Fintype.card (Idx T.dim) * n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, one_pos, fun γ _ h => absurd (Subsingleton.elim γ 0) h, by simp⟩
  have hf : (0 : ℝ) < fdeg E := by
    have h1 := ShortVectors.finrank_eq (E := E)
    have h2 : 0 < Module.finrank ℚ E := Module.finrank_pos
    exact_mod_cast (by omega : 0 < fdeg E)
  have hr : 0 < rdE E := Real.rpow_pos_of_pos
    (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero E)) _
  have hρ : 0 < 2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E := by positivity
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  set ρ := 2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E with hρdef
  refine ⟨lam / ρ, by positivity, fun γ hγ h0 => ?_, ?_⟩
  · rw [div_le_iff₀' hρ]
    exact le_mul_norm_flat_of_selfDual T Λ' hfg hint hdual hmin hγ h0
  · rw [Fintype.card_prod, Fintype.card_fin, mul_comm n, Nat.cast_mul, ← mul_assoc]
    congr 2
    field_simp


open Classical in
theorem norm_sum_jet_isogeny_sum_le (T : PT E) (w₀ : 𝓞 E) (hw : (w₀ : E) + cc (w₀ : E) = 1)
    (heps : ∀ x ∈ T.L, (T.eps x : ℝ) = Real.cos (Real.pi * (Hf x (act w₀ x)).im))
    (Λ' : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ')
    (R : Finset (Fin n → Vsp T.dim)) (hR : ∀ y ∈ R, y ∈ tensorLat T Λ')
    (hR' : ∀ y ∈ tensorLat T Λ', ∃! r, r ∈ R ∧ ∀ k, y k - r k ∈ T.L)
    (F : (Fin n → Vsp T.dim) → ℂ) (hF : F ∈ T.Sec 1 n)
    (lam : ℝ) (hlam : 0 < lam) (hmin : ∀ γ ∈ T.L, γ ≠ 0 → lam ≤ ‖γ‖)
    {κ : Type} (J : Finset κ) (c : κ → ℂ) (hc : ∀ j ∈ J, ‖c j‖ ≤ 1) (y : κ → Fin n → Vsp T.dim)
    (P : MvPolynomial (Letter n T.dim) ℂ) (a : ℕ) (hP : P.IsHomogeneous a) :
    ‖∑ j ∈ J, c j * polyDeriv P dir (T.U 1 (y j) (∑ r ∈ R, tensorEps w₀ r • T.U 1 r F)) 0‖ ≤
      J.card * (∑ m ∈ P.support, ‖P.coeff m‖) * (Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) *
        Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * Fintype.card (Idx T.dim) * n) *
          (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) / (Real.sqrt Real.pi * lam)) ^
          (Fintype.card (Idx T.dim) * n) * Real.sqrt (R.card * T.l2 1 F) := by
  obtain ⟨Y', hY', hka'⟩ := exists_tensorTorus (X := T) hfg hint hdual w₀
  obtain ⟨hm, hl⟩ := isogeny_sum_tensorLat T w₀ hw heps Λ' hfg hint hdual R hR hR' F hF Y' hY' hka'
  obtain ⟨lam', hlam', hmin', hC⟩ := exists_min_period T Λ' hfg hint hdual hlam hmin
  set U : ℕ → EuclideanSpace ℂ (Fin n × Idx T.dim) → (EuclideanSpace ℂ (Fin n × Idx T.dim) → ℂ) →
      EuclideanSpace ℂ (Fin n × Idx T.dim) → ℂ := fun q a G v =>
    cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * G (v - a) with hUdef
  have hU : ∀ (q : ℕ) a G v,
      U q a G v = cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * G (v - a) :=
    fun _ _ _ _ => rfl
  have key := theta_value_bound sup_le_l2_principal_torus U hU Y' _ hm lam' hlam'
    (fun x hx h0 => by
      obtain ⟨γ, rfl⟩ := (flat (n := n) (ι := Idx T.dim)).surjective x
      exact hmin' γ ((hY' γ).1 hx) fun h => h0 (by rw [h, map_zero]))
    J c hc (fun j => flat (y j)) P a hP
  rw [hl, hC] at key
  refine le_of_eq_of_le ?_ (key.trans_eq (by ring))
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [translate_comp_flat_symm T U hU, ← polyDeriv_comp_flat_symm, map_zero]
  congr!

end GlobalTheory.TensorLat

namespace GlobalTheory

open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD TensorLat


open Classical in
theorem normalised_theta_value_bound {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (T : PT E) (w₀ : 𝓞 E) (hw : (w₀ : E) + cc (w₀ : E) = 1)
    (heps : ∀ x ∈ T.L, (T.eps x : ℝ) = Real.cos (Real.pi * (Hf x (act w₀ x)).im))
    (s : (Fin 1 → Vsp T.dim) → ℂ) (hs : s ∈ T.Sec 1 1) (hs0 : s ≠ 0)
    (Λ' : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ')
    (R : Finset (Fin n → Vsp T.dim)) (hR : ∀ y ∈ R, y ∈ tensorLat T Λ')
    (hR' : ∀ y ∈ tensorLat T Λ', ∃! r, r ∈ R ∧ ∀ k, y k - r k ∈ T.L)
    (β : ℂ) (hβ : ‖β‖ ^ 2 = R.card)
    (lam : ℝ) (hlam : 0 < lam) (hmin : ∀ γ ∈ T.L, γ ≠ 0 → lam ≤ ‖γ‖)
    {κ : Type} (J : Finset κ) (c : κ → ℂ) (hc : ∀ j ∈ J, ‖c j‖ ≤ 1) (y : κ → Fin n → Vsp T.dim)
    (P : MvPolynomial (Letter n T.dim) ℂ) (a : ℕ) (hP : P.IsHomogeneous a) :
    β ≠ 0 ∧ 0 < T.l2 1 s ∧
    ‖β⁻¹ * ∑ j ∈ J, c j * polyDeriv P dir (T.U 1 (y j)
        (∑ r ∈ R, tensorEps w₀ r • T.U 1 r (ReciprocityTheory.ChartRestriction.G.I2.tens T fun _ => s))) 0‖ /
        Real.sqrt (T.l2 1 s) ^ n ≤
      J.card * (∑ m ∈ P.support, ‖P.coeff m‖) * (Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) *
        Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * Fintype.card (Idx T.dim) * n) *
          (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) / (Real.sqrt Real.pi * lam)) ^
          (Fintype.card (Idx T.dim) * n) := by
  have hl : 0 < T.l2 1 s := ThetaBound.l2_pos_of_mem_sec_of_ne_zero T le_rfl hs hs0
  have hRpos : 0 < R.card := by
    obtain ⟨r, ⟨hr, -⟩, -⟩ := hR' 0 (Submodule.zero_mem _)
    exact Finset.card_pos.2 ⟨r, hr⟩
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [norm_zero, zero_pow two_ne_zero] at hβ
    exact hRpos.ne (by exact_mod_cast hβ)
  refine ⟨hβ0, hl, ?_⟩
  have key := norm_sum_jet_isogeny_sum_le T w₀ hw heps Λ' hfg hint hdual R hR hR'
    (ReciprocityTheory.ChartRestriction.G.I2.tens T fun _ => s) (tens_mem T fun _ => hs) lam hlam hmin J c hc y P a hP
  have hsq : Real.sqrt (R.card * T.l2 1 (ReciprocityTheory.ChartRestriction.G.I2.tens T fun _ : Fin n => s)) =
      ‖β‖ * Real.sqrt (T.l2 1 s) ^ n := by
    rw [l2_tens_eq_prod, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← hβ,
      Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), mul_mul_mul_comm, ← mul_pow,
      Real.mul_self_sqrt hl.le, sq]
  have hb : 0 < ‖β‖ := norm_pos_iff.2 hβ0
  have hs' : 0 < Real.sqrt (T.l2 1 s) ^ n := pow_pos (Real.sqrt_pos.2 hl) n
  rw [hsq] at key
  rw [norm_mul, norm_inv, div_le_iff₀ hs', inv_mul_le_iff₀ hb]
  exact key.trans_eq (by ring)

end GlobalTheory
end
