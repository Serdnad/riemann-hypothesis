module

public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import ReciprocityTheory.DualLattices.Bundle011
public import Formalism.IncomingBounds.Bundle002
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ConstantCoeffSubstSame
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle033
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle049
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.DualLattices.Bundle022
public import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem place_mul_bar {p : ℕ} [Fact p.Prime] {OE : Type} [CommRing OE] [StarRing OE] (w : Place p OE)
    (hinv : ∀ x, sig p OE (sig p OE x) = x) : w.e * w.bar = 0 := by
  have hb : w.bar * w.bar = w.bar := by
    unfold Place.bar
    rw [← map_mul, w.idem]
  rcases w.prim (w.e * w.bar) (by rw [_root_.mul_mul_mul_comm, w.idem, hb])
    (by rw [mul_right_comm, w.idem]) with h | h
  · exact h
  · exfalso
    apply w.split
    have h2 := congrArg (sig p OE) h
    unfold Place.bar at h h2
    rw [map_mul, hinv, mul_comm, h] at h2
    exact h2.symm

theorem abelian_coker_bound : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp), H.P = 0 → H.PL = 0 → ∀ (w : Place p OE) (t : Fin w.n ≃ Emb (O := O) w.e) (rm : ℕ), (∀ τ ∈ Emb (O := O) w.bar, eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) ((algebraMap O C).comp τ) ≤ rm) → ∃ cw : NNReal, HasLen v O (htCoker H w.e w.bar) cw ∧ (v (algebraMap O C (p : O)) : ℝ) ^ (((w.n : ℝ) * rm) / ((p : ℝ) - 1)) ≤ cw := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _ _ _ _ _ cp hS g H hP hPL w t rm hrm
  obtain ⟨-, -, hstar⟩ := GlobalTheory.ChF.embeddings_idempotents_conjugation p C v O hv OE
  have hsig : ∀ x, sig p OE x = sigE p OE x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  have hinv : ∀ x, sig p OE (sig p OE x) = x := fun x => by rw [hsig, hsig, hS.invol]
  have h0 : w.e * w.bar = 0 := place_mul_bar w hinv
  have he := w.idem
  have hbar : sigE p OE w.e = w.bar := (hsig _).symm
  have hbar' : sigE p OE w.bar = w.e := by rw [← hbar, hS.invol]
  have hb : w.bar * w.bar = w.bar := by rw [← hbar, ← map_mul, w.idem]
  let c : OE →+* OE := ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom
  have hcc : ∀ τ : OE →+* O, (τ.comp c).comp c = τ := fun τ => by
    ext a
    simp [c]
  let s : Emb (O := O) w.e ≃ Emb (O := O) w.bar :=
    { toFun := fun τ => ⟨τ.1.comp c, by
        have := τ.2
        simp only [Emb, Set.mem_setOf_eq] at this ⊢
        rw [(hstar τ.1 w.bar).1, hbar', this]⟩
      invFun := fun τ => ⟨τ.1.comp c, by
        have := τ.2
        simp only [Emb, Set.mem_setOf_eq] at this ⊢
        rw [(hstar τ.1 w.e).1, hbar, this]⟩
      left_inv := fun τ => Subtype.ext (hcc τ.1)
      right_inv := fun τ => Subtype.ext (hcc τ.1) }
  have hd := GlobalTheory.T.range_idempotent_rank_sum_eigenspaceDim p C v O hv OE g H.ρL w.bar hb w.n (t.trans s)
  obtain ⟨cw, hcw⟩ : ∃ x, HasLen v O (htCoker H w.e w.bar) x :=
    lenEx C v O hv g H.Ht (H.ρL w.e) ((H.ρ w.bar).map (algebraMap ℤ_[p] O))
  refine ⟨cw, hcw, ?_⟩
  have hav := lengthDegree_abelianVariety p g C v O _ _ cp hS H 3 ![w.e, w.bar, 1 - w.e - w.bar] (Equiv.swap 0 1)
    (by
      intro i j
      fin_cases i <;> fin_cases j <;> simp <;>
        first
        | exact he
        | exact hb
        | linear_combination h0
        | linear_combination -he - h0
        | linear_combination -hb - h0
        | linear_combination he + hb + 2 * h0)
    (by
      intro i
      fin_cases i
      · simpa using hbar
      · simpa using hbar'
      · have : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
        simp only [Fin.reduceFinMk, this, Matrix.cons_val, map_sub, map_one, hbar, hbar']
        ring)
    (by simp [Fin.sum_univ_three, hP]) (by simp [hP])
    (by simp [Fin.sum_univ_three, hPL]) (by simp [hPL])
    0 (by decide) _ hd cw hcw
  refine le_trans ?_ hav
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  refine Real.rpow_le_rpow_of_exponent_ge ?_ ?_ ?_
  · exact_mod_cast pos_iff_ne_zero.2 hS.p_ne
  · exact_mod_cast hS.p_lt.le
  · refine div_le_div_of_nonneg_right ?_ (by linarith)
    have := Finset.sum_le_card_nsmul Finset.univ _ rm (fun j _ => hrm _ ((t.trans s) j).2)
    simp only [Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
    exact_mod_cast this

end GlobalTheory.ChF
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.DerivJet

variable {C : Type} [Field C] {W : Type} [Fintype W]

theorem jetAt0_mul_lin (c : W → C) (Q : MvPolynomial W C) (G : MvPowerSeries W C) :
    jetAt0 (Q * ∑ w, MvPolynomial.C (c w) * MvPolynomial.X w) G =
      jetAt0 Q (∑ w, c w • MvPowerSeries.pderiv (R := C) w G) := by
  rw [Finset.mul_sum, GlobalTheory.MinorShiftJet.jetAt0_sum_left, GlobalTheory.MinorShiftJet.jetAt0_sum_smul_right]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [mul_left_comm, GlobalTheory.MinorShiftJet.jetAt0_C_mul, GlobalTheory.MinorShiftJet.jetAt0_mul_X]

theorem jetAt0_iterate {A : Type} (S : A → MvPowerSeries W C) (D : A → A) (c : W → C) (k : ℕ)
    (h : k ≠ 0 → ∀ G, S (D G) = ∑ w, c w • MvPowerSeries.pderiv (R := C) w (S G)) (Q : MvPolynomial W C) (G : A) :
    jetAt0 Q (S (D^[k] G)) = jetAt0 (Q * (∑ w, MvPolynomial.C (c w) * MvPolynomial.X w) ^ k) (S G) := by
  induction k generalizing G with
  | zero => simp
  | succ k ih =>
    have h' := h (Nat.succ_ne_zero k)
    rw [Function.iterate_succ_apply, ih (fun _ => h'), h', ← jetAt0_mul_lin, pow_succ, mul_assoc]

theorem jetAt0_foldr {A ι : Type} (S : A → MvPowerSeries W C) (D : ι → A → A) (c : ι → W → C) (m : ι → ℕ)
    (h : ∀ l, m l ≠ 0 → ∀ G, S (D l G) = ∑ w, c l w • MvPowerSeries.pderiv (R := C) w (S G)) (L : List ι)
    (Q : MvPolynomial W C) (G : A) :
    jetAt0 Q (S (L.foldr (fun l g => (D l)^[m l] g) G)) =
      jetAt0 (Q * (L.map fun l => (∑ w, MvPolynomial.C (c l w) * MvPolynomial.X w) ^ m l).prod) (S G) := by
  induction L generalizing Q with
  | nil => simp
  | cons l L ih =>
    rw [List.foldr_cons, jetAt0_iterate S (D l) (c l) (m l) (h l), ih, List.map_cons, List.prod_cons, mul_assoc]

theorem jetAt0_one_left {σ : Type} (G : MvPowerSeries σ C) :
    jetAt0 1 G = MvPowerSeries.constantCoeff G := by
  rw [← MvPolynomial.C_1, ← MvPolynomial.monomial_zero', GlobalTheory.MinorShiftJet.jetAt0_monomial]
  simp [mfact]

theorem constantCoeff_DpolyN_eq_jetAt0 : ∀ (C : Type) [Field C] (dd n : ℕ) (F : Fin dd → PS C 2 dd) (ι : Type) [Fintype ι] (cp : ι → Fin n) (uv : ι → Fin dd → C) (W : Type) [Fintype W] (E : Fin n × Fin dd → MvPowerSeries W C), (∀ s, MvPowerSeries.constantCoeff (E s) = 0) → ∀ (co : ι → W → C) (P : MvPolynomial ι C), (∀ ℓ ∈ P.vars, ∀ G : PS C n dd, MvPowerSeries.subst E (DofN F (cp ℓ) (uv ℓ) G) = ∑ w, co ℓ w • MvPowerSeries.pderiv (R := C) w (MvPowerSeries.subst E G)) → ∀ G : PS C n dd, MvPowerSeries.constantCoeff (DpolyN F cp uv P G) = jetAt0 (MvPolynomial.aeval (fun ℓ => ∑ w, MvPolynomial.C (co ℓ w) * MvPolynomial.X w) P : MvPolynomial W C) (MvPowerSeries.subst E G) := by
  intro C _ dd n F ι _ cp uv W _ E hE co P h G
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', GlobalTheory.MinorShiftJet.jetAt0_sum_left, DpolyN, map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [map_mul, MvPowerSeries.constantCoeff_C, MvPolynomial.algebraMap_eq, GlobalTheory.MinorShiftJet.jetAt0_C_mul]
  congr 1
  rw [← cc_subst hE, ← jetAt0_one_left, DmonN,
    jetAt0_foldr (fun g => MvPowerSeries.subst E g) (fun l => DofN F (cp l) (uv l)) co m
      (fun l hl => h l ((MvPolynomial.mem_vars_iff_mem_support l).2 ⟨m, hm, Finsupp.mem_support_iff.2 hl⟩)),
    one_mul, Finset.prod_map_toList]

end GlobalTheory.DerivJet
end

section

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory

section NabLin

variable {R : Type} [CommRing R] {d n : ℕ}

theorem dofN_add (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (f g : PS R n d) :
    DofN F b u (f + g) = DofN F b u f + DofN F b u g := by
  simp only [DofN, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem dofN_smul (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (t : R) (f : PS R n d) :
    DofN F b u (t • f) = t • DofN F b u f := by
  simp only [DofN, Derivation.map_smul, map_smul, mul_smul_comm, Finset.smul_sum]

theorem dofN_iterate_add (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (k : ℕ)
    (f g : PS R n d) :
    (DofN F b u)^[k] (f + g) = (DofN F b u)^[k] f + (DofN F b u)^[k] g := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, dofN_add]

theorem dofN_iterate_smul (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (k : ℕ)
    (t : R) (f : PS R n d) :
    (DofN F b u)^[k] (t • f) = t • (DofN F b u)^[k] f := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, dofN_smul]

variable {ι : Type} [Fintype ι]

theorem dmonN_add (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R) (m : ι →₀ ℕ)
    (f g : PS R n d) :
    DmonN F cp u m (f + g) = DmonN F cp u m f + DmonN F cp u m g := by
  unfold DmonN
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons, ih, dofN_iterate_add]

theorem dmonN_smul (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R) (m : ι →₀ ℕ)
    (t : R) (f : PS R n d) :
    DmonN F cp u m (t • f) = t • DmonN F cp u m f := by
  unfold DmonN
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons, ih, dofN_iterate_smul]

theorem dpolyN_eq_sum_of_subset (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)
    (P : MvPolynomial ι R) (f : PS R n d) (s : Finset (ι →₀ ℕ)) (hs : P.support ⊆ s) :
    DpolyN F cp u P f = ∑ m ∈ s, MvPowerSeries.C (P.coeff m) * DmonN F cp u m f := by
  unfold DpolyN
  refine Finset.sum_subset hs fun m _ hm => ?_
  rw [MvPolynomial.notMem_support_iff.mp hm, map_zero, zero_mul]

theorem dpolyN_add_right (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)
    (P : MvPolynomial ι R) (f g : PS R n d) :
    DpolyN F cp u P (f + g) = DpolyN F cp u P f + DpolyN F cp u P g := by
  simp only [DpolyN, dmonN_add, mul_add, Finset.sum_add_distrib]

theorem dpolyN_smul_right (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)
    (P : MvPolynomial ι R) (t : R) (f : PS R n d) :
    DpolyN F cp u P (t • f) = t • DpolyN F cp u P f := by
  simp only [DpolyN, dmonN_smul, mul_smul_comm, Finset.smul_sum]

theorem dpolyN_add_left (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)
    (P Q : MvPolynomial ι R) (f : PS R n d) :
    DpolyN F cp u (P + Q) f = DpolyN F cp u P f + DpolyN F cp u Q f := by
  classical
  rw [dpolyN_eq_sum_of_subset F cp u (P + Q) f (P.support ∪ Q.support) MvPolynomial.support_add,
    dpolyN_eq_sum_of_subset F cp u P f (P.support ∪ Q.support) Finset.subset_union_left,
    dpolyN_eq_sum_of_subset F cp u Q f (P.support ∪ Q.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add, map_add (f := _), add_mul]

theorem dpolyN_C_mul_left (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)
    (t : R) (P : MvPolynomial ι R) (f : PS R n d) :
    DpolyN F cp u (MvPolynomial.C t * P) f = MvPowerSeries.C t * DpolyN F cp u P f := by
  have hs : (MvPolynomial.C t * P).support ⊆ P.support := by
    intro m hm
    rw [MvPolynomial.mem_support_iff] at hm ⊢
    intro h0
    exact hm (by rw [MvPolynomial.coeff_C_mul, h0, mul_zero])
  rw [dpolyN_eq_sum_of_subset F cp u _ f P.support hs, DpolyN, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_C_mul, map_mul, mul_assoc]

end NabLin

theorem nabValN_bilinear : ∀ (K : Type) [CommRing K] [Algebra ℚ K] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB K d O) (h : PS K 2 d) (w0 : O) (m n : ℕ) (ι : Type) [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → K), (∀ (f g : PS K n d) (P : MvPolynomial ι K), nabValN B K h w0 m (f + g) cp u P = nabValN B K h w0 m f cp u P + nabValN B K h w0 m g cp u P) ∧ (∀ (t : K) (f : PS K n d) (P : MvPolynomial ι K), nabValN B K h w0 m (t • f) cp u P = t * nabValN B K h w0 m f cp u P) ∧ (∀ (f : PS K n d) (P Q : MvPolynomial ι K), nabValN B K h w0 m f cp u (P + Q) = nabValN B K h w0 m f cp u P + nabValN B K h w0 m f cp u Q) ∧ (∀ (t : K) (f : PS K n d) (P : MvPolynomial ι K), nabValN B K h w0 m f cp u (MvPolynomial.C t * P) = t * nabValN B K h w0 m f cp u P) := by
  intro K _ _ d O _ _ B h w0 m n ι _ cp u
  refine ⟨fun f g P => ?_, fun t f P => ?_, fun f P Q => ?_, fun t f P => ?_⟩
  · simp only [nabValN, add_mul, dpolyN_add_right, map_add (f := _)]
  · simp only [nabValN]
    rw [smul_mul_assoc, dpolyN_smul_right, MvPowerSeries.smul_eq_C_mul, map_mul,
      MvPowerSeries.constantCoeff_C]
  · simp only [nabValN, dpolyN_add_left, map_add (f := _)]
  · simp only [nabValN]
    rw [dpolyN_C_mul_left, map_mul, MvPowerSeries.constantCoeff_C]

end GlobalTheory
end
