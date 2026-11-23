module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle644
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle703
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle047
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle667
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle701
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle705
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosureBaseChangeMapsAndRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle702
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem exists_clopen_kerStableAt : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ ∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ W ↔ KerStableAt o ψ t := by
  intro p _ D R _ b N c Y s o B _ _ ψ ψ' hp ⟨e, he⟩ hB hq
  have hc : IsUnit (c : Γ(Y, ⊤)) := by
    have := (hp.pow e).map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rw [← Nat.cast_pow, map_natCast, ← he] at this
    exact this
  haveI : IsMonHom ψ := hq.1
  haveI : IsMonHom ψ' := hq.2.1
  haveI := D.finO
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℤ) (M := D.O)
  have key : ∀ a : D.O, ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ ∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y),
      Set.range t.base ⊆ W ↔ ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom → ∀ g : T ⟶ o.A,
        g ^ c = 1 → g ≫ ψ = 1 → g ≫ o.act.act a ≫ ψ = 1 := by
    intro a
    haveI := o.act.hom a
    obtain ⟨W, hW1, hW2, hW, -⟩ := GlobalTheory.LevCover.kerlocus_open_closed Y o.A c Unit (fun _ => B) (fun _ => ψ) B
      (o.act.act a ≫ ψ) o.ab (fun _ => hB) hB (fun _ => inferInstance) inferInstance hc
    refine ⟨W, hW1, hW2, fun Tb t => (hW Tb t).trans ?_⟩
    simp only [forall_const]
  choose W hW1 hW2 hW using key
  have hkill : ∀ (T : Over Y) (g : T ⟶ o.A), g ≫ ψ = 1 → g ^ c = 1 := by
    intro T g hg
    have h1 : g ^ c = g ≫ (𝟙 o.A) ^ c := by rw [MonObj.comp_pow, Category.comp_id]
    rw [h1, ← hq.2.2.1, ← Category.assoc, hg, MonObj.one_comp]
  refine ⟨⋂ a ∈ S, W a, isOpen_biInter_finset (fun a _ => hW1 a),
    isClosed_iInter fun a => isClosed_iInter fun _ => hW2 a, fun Tb t => ?_⟩
  rw [Set.subset_iInter₂_iff]
  constructor
  · intro h T σ hσ g hg a
    let f : D.O →+ Additive (T ⟶ B) := AddMonoidHom.mk' (fun a => Additive.ofMul (g ≫ o.act.act a ≫ ψ))
      (fun a a' => by
        rw [o.act.add]
        haveI := o.act.hom a
        haveI := o.act.hom a'
        rw [MonObj.mul_comp, MonObj.comp_mul]
        rfl)
    have hSk : (S : Set D.O) ⊆ (f.toIntLinearMap.ker : Set D.O) := fun a ha => by
      have := (hW a Tb t).1 (h a ha) T σ hσ g (hkill T g hg) hg
      simp [f, this]
    have htop : (⊤ : Submodule ℤ D.O) ≤ LinearMap.ker f.toIntLinearMap := by
      rw [← hS]; exact Submodule.span_le.mpr hSk
    have ha : f a = 0 := htop Submodule.mem_top
    simpa [f] using ha
  · intro h a _
    exact (hW a Tb t).2 fun T σ hσ g _ hg => h T σ hσ g hg a

end GlobalTheory.UPel.HT.ES
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

namespace GlobalTheory.ThetaTransform

theorem continuous_thV : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)]
    (ψ : AddChar (AF F) ℂ), IsTotallyReal F → IsCharAF F ψ → ∀ Φ : (Fin N → AF F) → ℂ, Decay Φ →
      Continuous (thV ψ Φ) := by
  intro F _ _ N _ ψ hF hψ Φ hΦ
  obtain ⟨hc, ⟨K, hK, hKz⟩, hdec⟩ := hΦ
  obtain ⟨hψc, hψn, -, -⟩ := hψ
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  obtain ⟨k, hk⟩ := GlobalTheory.SumMaj.summable_majorant F N hF K hK
  obtain ⟨C, hC⟩ := hdec k
  have hC0 : 0 ≤ C :=
    le_trans (mul_nonneg (norm_nonneg _) (pow_nonneg (by linarith [GlobalTheory.SumMaj.sz_nonneg (0 : Fin N → AF F)]) k))
      (hC 0)
  have hterm : ∀ ξ : Fin N → F, Continuous fun w : VA F N =>
      ψ (rat ξ ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) * Φ (rat ξ + w.1) := by
    intro ξ
    refine Continuous.mul (hψc.comp ?_) (hc.comp (continuous_const.add continuous_fst))
    refine Continuous.add ?_ (continuous_const.mul ?_)
    · exact continuous_finsetSum _ fun i _ => continuous_const.mul ((continuous_apply i).comp continuous_snd)
    · exact continuous_finsetSum _ fun i _ =>
        ((continuous_apply i).comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)
  have heq : thV ψ Φ = fun w : VA F N => ∑' ξ : Fin N → F,
      ψ (rat ξ ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) * Φ (rat ξ + w.1) := by
    funext w
    simp only [thV, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.schr]
    rfl
  rw [heq]
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨ω, hωc, hωn⟩ := exists_compact_mem_nhds x
  obtain ⟨c, hcs, hc0, hcb⟩ := hk (Prod.fst '' ω) (hωc.image continuous_fst)
  have hon : ContinuousOn (fun w : VA F N => ∑' ξ : Fin N → F,
      ψ (rat ξ ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) * Φ (rat ξ + w.1)) ω := by
    refine continuousOn_tsum (fun ξ => (hterm ξ).continuousOn) (hcs.mul_left C) fun ξ w hw => ?_
    rw [norm_mul, hψn, one_mul]
    by_cases hmem : fin (rat ξ + w.1) ∈ K
    · have h1 := hcb ξ w.1 ⟨w, hw, rfl⟩ hmem
      have h2 := hC (rat ξ + w.1)
      calc ‖Φ (rat ξ + w.1)‖ = ‖Φ (rat ξ + w.1)‖ * 1 := (mul_one _).symm
        _ ≤ ‖Φ (rat ξ + w.1)‖ * (c ξ * (1 + sz (rat ξ + w.1)) ^ k) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = c ξ * (‖Φ (rat ξ + w.1)‖ * (1 + sz (rat ξ + w.1)) ^ k) := by ring
        _ ≤ c ξ * C := mul_le_mul_of_nonneg_left h2 (hc0 ξ)
        _ = C * c ξ := mul_comm _ _
    · rw [hKz _ hmem, norm_zero]
      exact mul_nonneg hC0 (hc0 ξ)
  exact hon.continuousAt hωn

end GlobalTheory.ThetaTransform
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem _root_.GlobalTheory.T.factors_through_zero_locus : ∀ (Rg : Type) [CommRing Rg] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) Rg)) (T : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin n) Rg)), (∃ w : T ⟶ Sp (MvPolynomial (Fin n) Rg ⧸ I), w ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = g) ↔ ∀ P ∈ I, GlobalTheory.FormsLocus.ringOf g P = 0 := by
  first | (exact @GlobalTheory.FormsLocus.factors_quot_iff) | (exact GlobalTheory.FormsLocus.factors_quot_iff) | (intros; apply GlobalTheory.FormsLocus.factors_quot_iff  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem _root_.GlobalTheory.T.germ_constants_eq_along_affineSpace_square : ∀ (Rg : Type) [CommRing Rg] (A₀ T X : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (n : ℕ) (g : T ⟶ Sp (MvPolynomial (Fin n) Rg)) (φ : X ⟶ A₀) (p : X ⟶ T), φ ≫ f = p ≫ g ≫ affπ Rg n → ∀ (z : X) (r : Rg), gs φ z ⊤ (GlobalTheory.FormsLocus.cstT f r) = gs p z ⊤ (GlobalTheory.FormsLocus.ringOf g (MvPolynomial.C r)) := by
  first | (exact @GlobalTheory.FormsLocus.germ_cstT_eq_germ_ringOf_C) | (exact GlobalTheory.FormsLocus.germ_cstT_eq_germ_ringOf_C) | (intros; apply GlobalTheory.FormsLocus.germ_cstT_eq_germ_ringOf_C <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem _root_.GlobalTheory.T.section_local_expansion : ∀ (Rg : Type) [CommRing Rg] (A₀ X : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (M : LB A₀) (Q : GlobalTheory.AbLaw.Perf f M) (s : LB.Sec M) (φ : X ⟶ A₀) (z : X) (i : Q.I), φ z ∈ Q.W i → gs φ z (M.U (Q.ch i)) (s.f (Q.ch i)) = ∑ k, gs φ z ⊤ (GlobalTheory.FormsLocus.cstT f (GlobalTheory.FormsLocus.vecOf Q s k)) * gs φ z (Q.W i) (Q.u k i) := by
  first | (exact @GlobalTheory.FormsLocus.VecGerm.germ_eq_sum_vecOf) | (exact GlobalTheory.FormsLocus.VecGerm.germ_eq_sum_vecOf) | (intros; apply GlobalTheory.FormsLocus.VecGerm.germ_eq_sum_vecOf <;> assumption)
end

section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

namespace GlobalTheory.CharPair.FirstBlock

section General

variable {K A : Type} [CommRing K] [CommRing A] [Algebra K A]

theorem der_aeval {σ : Type} [Fintype σ] [DecidableEq σ] (d : Derivation K A A) (z : σ → A)
    (G : MvPolynomial σ K) : d (aeval z G) = ∑ i, aeval z (pderiv i G) * d (z i) := by
  induction G using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p n hp =>
    have e : ∀ i, aeval z (pderiv i (p * X n)) * d (z i) =
        (if n = i then aeval z p * d (z i) else 0) + z n * (aeval z (pderiv i p) * d (z i)) := by
      intro i
      by_cases hi : n = i
      · subst hi
        simp [Derivation.leibniz]; ring
      · simp [Derivation.leibniz, hi, pderiv_X, Pi.single_apply]; ring
    simp only [e, Finset.sum_add_distrib]
    simp [hp, Finset.mul_sum]

theorem der_prod {ι : Type} [DecidableEq ι] (d : Derivation K A A) (s : Finset ι) (f : ι → A) :
    d (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * d (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Derivation.leibniz, ih, Finset.erase_insert ha,
      smul_eq_mul, smul_eq_mul, add_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hne : a ≠ i := fun e => ha (e ▸ hi)
    rw [Finset.erase_insert_of_ne hne, Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h)),
      mul_assoc]

theorem der_det {n : Type} [Fintype n] [DecidableEq n] (d : Derivation K A A) (M : Matrix n n A) :
    d M.det = ∑ i, (M.updateRow i fun j => d (M i j)).det := by

  simp only [Matrix.det_apply, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Finset.smul_sum, Units.smul_def, Units.smul_def, map_zsmul, der_prod,
    ← Equiv.sum_comp σ (fun i => ∏ x, (M.updateRow i fun j => d (M i j)) (σ x) x)]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Matrix.updateRow_self]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Matrix.updateRow_ne (fun e => (Finset.mem_erase.1 hj).1 (σ.injective e))]

end General

variable {P Q R : ℕ}

noncomputable def rowDer (Q R : ℕ) (a a' : Fin P) : Derivation ℂ (Pol P Q R 0) (Pol P Q R 0) :=
  ∑ c : Fin R, (X (Sum.inl a, Sum.inl c) : Pol P Q R 0) • pderiv (Sum.inl a', Sum.inl c)

theorem rowDer_apply (a a' : Fin P) (F : Pol P Q R 0) :
    rowDer Q R a a' F = ∑ c : Fin R, X (Sum.inl a, Sum.inl c) * pderiv (Sum.inl a', Sum.inl c) F := by
  have := map_sum (Derivation.coeFnAddMonoidHom (R := ℂ) (A := Pol P Q R 0) (M := Pol P Q R 0))
    (fun c : Fin R => (X (Sum.inl a, Sum.inl c) : Pol P Q R 0) • pderiv (Sum.inl a', Sum.inl c)) Finset.univ
  have h2 := congrFun this F
  rw [Finset.sum_apply] at h2
  exact h2

theorem rowDer_X_inl_inl (a a' i : Fin P) (c : Fin R) :
    rowDer Q R a a' (X (Sum.inl i, Sum.inl c)) = if i = a' then X (Sum.inl a, Sum.inl c) else 0 := by
  rw [rowDer_apply]
  by_cases h : i = a' <;> simp [pderiv_X, Pi.single_apply, h]

theorem rowDer_w (a a' : Fin P) (b : Fin Q) (c : Fin R) :
    rowDer Q R a a' (X (Sum.inr b, Sum.inl c)) = 0 := by
  rw [rowDer_apply]
  simp [pderiv_X, Pi.single_apply]

theorem rowDer_mR (a a' i : Fin P) (b : Fin Q) :
    rowDer Q R a a' (mR P Q R i b) = if i = a' then mR P Q R a b else 0 := by

  simp only [mR, map_sum, Derivation.leibniz, rowDer_X_inl_inl, rowDer_w, smul_eq_mul]
  split_ifs <;> simp [mul_comm]

theorem rowDer_detR (h : P ≤ R) (a a' : Fin P) :
    rowDer Q R a a' (detR P Q R h) = if a = a' then detR P Q R h else 0 := by
  rw [detR, der_det, Finset.sum_eq_single a']
  · simp only [Matrix.of_apply, rowDer_X_inl_inl, if_true]
    split_ifs with e
    · subst e
      congr 1
      exact Matrix.updateRow_eq_self _ _
    · exact Matrix.det_updateRow_eq_zero (M := Matrix.of fun a c : Fin P =>
        (X (Sum.inl a, Sum.inl (Fin.castLE h c)) : Pol P Q R 0)) e
  · intro i _ hi
    simp only [Matrix.of_apply, rowDer_X_inl_inl, if_neg hi]
    exact Matrix.det_eq_zero_of_row_eq_zero i (by simp)
  · simp

theorem act_eq (a a' : Fin P) (F : Pol P Q R 0) :
    fockAct1 P Q R 0 (Eab (Sum.inl a) (Sum.inl a')) F =
      rowDer Q R a a' F + (if a = a' then (R : ℂ) / 2 else 0) • F := by
  have hpp : ∀ c : Fin R, omE (p := P) (q := Q) (r := R) (s := 0) (Sum.inl a, Sum.inl c) (Sum.inl a', Sum.inl c) F =
      X (Sum.inl a, Sum.inl c) * pderiv (Sum.inl a', Sum.inl c) F + (if a = a' then (1 / 2 : ℂ) else 0) • F := by
    intro c
    simp only [omE, raiB, lowB, linePos]
    by_cases e : a = a' <;> simp [e]
  rw [fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type, rowDer_apply]
  simp only [hpp, Finset.sum_add_distrib, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  split_ifs
  · congr 2; ring
  · simp

theorem act_first_block : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (a a' : Fin P) (G : Mdl P Q), fockAct1 P Q R 0 (Eab (Sum.inl a) (Sum.inl a')) (embR P Q R h k G) = embR P Q R h k (opR P Q R k (Sum.inl a) (Sum.inl a') G) := by
  intro P Q R h k a a' G
  have hk : rowDer Q R a a' (detR P Q R h ^ k) = (if a = a' then (k : ℂ) else 0) • detR P Q R h ^ k := by
    rw [Derivation.leibniz_pow, rowDer_detR]
    split_ifs
    · rcases k with _ | k
      · simp
      · rw [Nat.cast_smul_eq_nsmul, Nat.add_sub_cancel, smul_eq_mul, ← pow_succ]
    · simp
  have hG : rowDer Q R a a' (aeval (fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2) G) =
      ∑ b, mR P Q R a b * aeval (fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2) (pderiv (a', b) G) := by
    rw [der_aeval, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [rowDer_mR, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [mul_comm]
  have he : ∀ H, embR P Q R h k H =
      aeval (fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2) H * detR P Q R h ^ k := fun H => rfl
  have ho : opR P Q R k (Sum.inl a) (Sum.inl a') G =
      ∑ b, X (a, b) * pderiv (a', b) G + (if a = a' then (k : ℂ) + (R : ℂ) / 2 else 0) • G := by
    by_cases e : a = a' <;> simp [opR, LinearMap.sum_apply, e]

  rw [act_eq, he, he, ho, Derivation.leibniz, hk, hG, map_add (f := _), map_sum, map_smul]
  simp only [map_mul, aeval_X, smul_eq_mul, add_mul, mul_smul_comm, smul_mul_assoc]
  rw [mul_comm (detR P Q R h ^ k)]
  split_ifs
  · module
  · simp

end GlobalTheory.CharPair.FirstBlock
end

section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

namespace GlobalTheory.CharPair

theorem fockAct1_Eab_inl_inr_embR : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q),
    fockAct1 P Q R 0 (Eab (Sum.inl a) (Sum.inr b)) (embR P Q R h k G) =
      embR P Q R h k (opR P Q R k (Sum.inl a) (Sum.inr b) G) := by
  intro P Q R h k a b G
  rw [fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  have hterm : ∀ c : Fin R, omE ((Sum.inl a : Ix P Q), (Sum.inl c : Ix R 0)) (Sum.inr b, Sum.inl c)
      (embR P Q R h k G) = (X (Sum.inl a, Sum.inl c) * X (Sum.inr b, Sum.inl c)) * embR P Q R h k G := by
    intro c
    simp [omE, raiB, lowB, linePos, mul_assoc]
  simp only [hterm, ← Finset.sum_mul]
  simp only [opR, mulM, embR, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
    AlgHom.toLinearMap_apply, LinearMap.mulRight_apply, map_mul, aeval_X, mR]
  ring

end GlobalTheory.CharPair
end

section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

namespace GlobalTheory.CharPair.GradR

theorem detR_isHomogeneous (P Q R : ℕ) (h : P ≤ R) : (detR P Q R h).IsHomogeneous P := by
  unfold detR
  rw [Matrix.det_apply']
  refine IsHomogeneous.sum _ _ _ fun σ _ => ?_
  have h1 : (∏ i : Fin P, (Matrix.of fun a c : Fin P =>
      (X (Sum.inl a, Sum.inl (Fin.castLE h c)) : Pol P Q R 0)) (σ i) i).IsHomogeneous (∑ _i : Fin P, 1) :=
    IsHomogeneous.prod _ _ _ fun i _ => isHomogeneous_X ℂ _
  have h0 : (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : Pol P Q R 0).IsHomogeneous 0 := by
    have := isHomogeneous_C (Ix P Q × Ix R 0) (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)
    rwa [map_intCast] at this
  simpa using h0.mul h1

end GlobalTheory.CharPair.GradR
end

section

open GlobalTheory.LeviCut

namespace GlobalTheory.LeviCut

theorem adj_sub_of_adjBdd {A : Type} [Ring A] [Algebra ℚ A] (x y : A) : adj (x - y) = adj x - adj y := by
  ext T
  simp only [adj, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
  noncomm_ring

theorem adj_zero_of_adjBdd {A : Type} [Ring A] [Algebra ℚ A] : adj (0 : A) = 0 := by
  ext T
  simp [adj]

theorem adj_commutator_of_adjBdd {A : Type} [Ring A] [Algebra ℚ A] (x y : A) :
    adj x * adj y - adj y * adj x = adj (x * y - y * x) := by
  ext T
  simp only [adj, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
    map_sub]
  noncomm_ring

theorem adjBdd_holds : AdjBdd := by
  intro V _ _ N K e hrel hbdd hspan
  constructor
  · intro a b c d ha hb hc hd
    rw [adj_commutator_of_adjBdd, hrel a b c d ha hb hc hd, adj_sub_of_adjBdd]
    split_ifs <;> simp [adj_zero_of_adjBdd]
  · intro a ha b hb n T hT hn
    have hw : ∀ x ∈ {x : V | ∃ μ : ℕ → ℤ, IsWt N e μ x}, T x = (0 : Module.End ℚ V) x := by
      rintro x ⟨μ, hμ⟩
      simp only [LinearMap.zero_apply]
      by_cases hx : x = 0
      · simp [hx]
      have h1 : μ b - μ a ≤ K := by
        by_contra hlt
        push_neg at hlt
        apply hx
        apply hbdd b hb a ha (μ b - μ a) x _ hlt
        rw [hμ b hb, hμ a ha]
        push_cast
        rw [sub_smul]
      apply hbdd a ha b hb (μ a - μ b + n) (T x) _ (by push_cast at hn h1 ⊢; omega)
      have eq := LinearMap.congr_fun hT x
      simp only [adj, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
        Module.End.mul_apply, LinearMap.smul_apply, hμ a ha, hμ b hb, map_smul] at eq
      push_cast
      rw [add_smul, sub_smul, ← eq]
      abel
    exact LinearMap.ext_on hspan hw

end GlobalTheory.LeviCut
end

section

open IsLocalRing Polynomial
open scoped TensorProduct
open GlobalTheory.LocAcyc GlobalTheory.KeyOriginNoeth GlobalTheory.KeyOriginBC

theorem _root_.GlobalTheory.T.exists_closureBaseChange_maps_and_retraction : ∀ (A R A₁ R₁ : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    [CommRing A₁] [IsDomain A₁] [CommRing R₁] [Algebra A₁ R₁] (f : A →+* A₁), Function.Injective f →
    ∀ (κ : R →+* R₁), κ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp f →
    ∀ (β : GenFib A R →+* GenFib A₁ R₁),
    β.comp (algebraMap R (GenFib A R)) = (algebraMap R₁ (GenFib A₁ R₁)).comp κ →
    ∀ (DA : Type) [CommRing DA] [Algebra (GenFib A R) DA] [Algebra.IsIntegral (GenFib A R) DA]
    (S : Type) [CommRing S] [Algebra R₁ S],
    letI := closureAlg A R DA
    letI : Algebra R S := ((algebraMap R₁ S).comp κ).toAlgebra
    letI : Algebra R₁ (BC β DA) := (baseHom A₁ R₁ (BC β DA)).toAlgebra
    ∃ (φ : S ⊗[R] closure A R DA →ₐ[S] S ⊗[R₁] BC β DA)
      (ψ : S ⊗[R₁] BC β DA →ₐ[S] Localization (Algebra.algebraMapSubmonoid (S ⊗[R] closure A R DA)
          ((nonZeroDivisors A₁).map ((algebraMap R₁ S).comp (algebraMap A₁ R₁))))),
      ψ.comp φ = IsScalarTower.toAlgHom S _ _ ∧
      (∀ m ∈ (nonZeroDivisors A₁).map ((algebraMap R₁ S).comp (algebraMap A₁ R₁)),
        IsUnit (algebraMap S (S ⊗[R₁] BC β DA) m)) ∧
      ∀ x : S ⊗[R₁] BC β DA, ∃ m ∈ (nonZeroDivisors A₁).map ((algebraMap R₁ S).comp (algebraMap A₁ R₁)),
        x * algebraMap S _ m ∈ φ.range := by
  first | (exact @GlobalTheory.KeyOriginBCMaps.exists_bc_closure_maps) | (exact GlobalTheory.KeyOriginBCMaps.exists_bc_closure_maps) | (intros; apply GlobalTheory.KeyOriginBCMaps.exists_bc_closure_maps  <;> assumption)
end

section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

theorem _root_.GlobalTheory.T.wachModuleMapMatrix_comp_mul : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K LL : FinExt l) (hA : CaseA K LL) (T T' T'' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (n n' n'' : ℕ) (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T)) (b' : Module.Basis (Fin n') (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T')) (b'' : Module.Basis (Fin n'') (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T'')) (g : LatHom T.L T'.L) (g' : LatHom T'.L T''.L) (g'' : LatHom T.L T''.L) (A : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n' n) (A' : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n'' n') (A'' : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n'' n), IsMapMat (H.W K 1 LL hA.2.2) g b b' A → IsMapMat (H.W K 1 LL hA.2.2) g' b' b'' A' → IsMapMat (H.W K 1 LL hA.2.2) g'' b b'' A'' → (∀ x, g''.f x = g'.f (g.f x)) → ∀ i, A'' i = A' i * A i := by
  first | exact @GlobalTheory.WachPlace.isMapMat_comp_mul | exact GlobalTheory.WachPlace.isMapMat_comp_mul | (intros; apply GlobalTheory.WachPlace.isMapMat_comp_mul <;> assumption)
end
