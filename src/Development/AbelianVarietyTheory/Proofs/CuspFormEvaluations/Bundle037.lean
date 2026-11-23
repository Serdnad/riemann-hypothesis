module

import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsValueAtJetPointCmFrameSection
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FderivEqOfJetOf
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle036
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle034
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle023
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGeneratorNeZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal.JetCorr

theorem jet_point_eq {K : Type} [Field K] {J : Type} {m : ℕ} (p : PrimeSpectrum (Jet K J m)) :
    p = IsLocalRing.closedPoint (Jet K J m) := by
  apply GlobalTheory.JetVal.jet_pt_eq <;> assumption

section JetOf

variable {N : ℕ} (m : ℕ)

theorem jetOf_one' : jetOf m (fun _ : Fin N → ℂ => (1 : ℂ)) = 1 := by
  rw [jetOf_const, map_one]

theorem jetOf_pow' {F : (Fin N → ℂ) → ℂ} (hF : AnalyticAt ℂ F 0) (k : ℕ) :
    jetOf m (fun v => F v ^ k) = jetOf m F ^ k := by
  induction k with
  | zero => simpa using jetOf_one' m
  | succ k ih =>
    rw [pow_succ, ← ih, ← jetOf_mul m (hF.fun_pow k).contDiffAt hF.contDiffAt]
    congr 1

theorem jetOf_mul_inv {F : (Fin N → ℂ) → ℂ} (hF : AnalyticAt ℂ F 0) (h0 : F 0 ≠ 0) :
    jetOf m F * jetOf m (fun v => (F v)⁻¹) = 1 := by
  rw [← jetOf_mul m hF.contDiffAt (hF.fun_inv h0).contDiffAt, ← jetOf_one' m]
  refine jetOf_congr m ((hF.continuousAt.eventually_ne h0).mono fun v hv => ?_)
  exact mul_inv_cancel₀ hv

theorem jetOf_zpow {F : (Fin N → ℂ) → ℂ} (hF : AnalyticAt ℂ F 0) (h0 : F 0 ≠ 0)
    (u : (Jet ℂ (Fin 1 × Fin N) m)ˣ) (hu : u.val = jetOf m F) (a : ℤ) :
    jetOf m (fun v => F v ^ a) = (u ^ a).val := by
  obtain ⟨k, rfl | rfl⟩ := a.eq_nat_or_neg
  · simp only [zpow_natCast, Units.val_pow_eq_pow_val, hu]
    exact jetOf_pow' m hF k
  · simp only [zpow_neg, zpow_natCast]
    symm
    apply Units.inv_eq_of_mul_eq_one_right
    rw [Units.val_pow_eq_pow_val, hu, ← jetOf_pow' m hF k]
    exact jetOf_mul_inv m (hF.fun_pow k) (pow_ne_zero _ h0)

theorem jetOf_prod {K : Type} (s : Finset K) {F : K → (Fin N → ℂ) → ℂ} (hF : ∀ k, AnalyticAt ℂ (F k) 0) :
    jetOf m (fun v => ∏ k ∈ s, F k v) = ∏ k ∈ s, jetOf m (F k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using jetOf_one' m
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ← ih, ← jetOf_mul m (hF a).contDiffAt
      (Finset.analyticAt_fun_prod s fun k _ => hF k).contDiffAt]
    congr 1
    funext v
    simp [Finset.prod_insert ha]

end JetOf

theorem jetN_prod_zpow {n g : ℕ} (m : ℕ) {K : Type} [Fintype K] (f : K → (Fin g → ℂ) → ℂ)
    (hf : ∀ k, AnalyticAt ℂ (f k) 0) (h0 : ∀ k, f k 0 ≠ 0)
    (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (ε : K → ℤ) :
    ∃ u : K → (Jet ℂ (Fin n × Fin g) m)ˣ, (∀ k, (u k).val = jetN m fun w => f k (Λ k w)) ∧
      jetN m (fun w => ∏ k, f k (Λ k w) ^ ε k) = (∏ k, u k ^ ε k).val := by
  have hc : colsOf n g 0 = 0 := rfl
  have hA : ∀ k, AnalyticAt ℂ (fun v => f k (Λ k (colsOf n g v))) 0 := fun k => by
    have h1 : AnalyticAt ℂ (colsOf n g) 0 :=
      AnalyticAt.pi fun i => AnalyticAt.pi fun j =>
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n * g) => ℂ) (finProdFinEquiv (i, j))).analyticAt 0
    have h2 : AnalyticAt ℂ (fun v => Λ k (colsOf n g v)) 0 :=
      ((LinearMap.toContinuousLinearMap (Λ k)).analyticAt _).comp h1
    exact (hf k).comp_of_eq h2 (by rw [hc, map_zero])
  have hz : ∀ k, f k (Λ k (colsOf n g 0)) ≠ 0 := fun k => by rw [hc, map_zero]; exact h0 k
  let u0 : K → (Jet ℂ (Fin 1 × Fin (n * g)) m)ˣ := fun k =>
    Units.mkOfMulEqOne _ _ (jetOf_mul_inv m (hA k) (hz k))
  refine ⟨fun k => Units.map (renN n g m).toMonoidHom (u0 k), fun k => rfl, ?_⟩
  unfold jetN
  rw [jetOf_prod m Finset.univ (F := fun k v => f k (Λ k (colsOf n g v)) ^ ε k)
    fun k => (hA k).fun_zpow (hz k), map_prod, Units.coe_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [jetOf_zpow m (hA k) (hz k) (u0 k) rfl, ← map_zpow]
  rfl

open scoped Classical in
theorem prod_zpow_fiber {M T K : Type*} [CommGroup M] [Fintype K] (s : Finset T) (φ : K → T) (hs : ∀ k, φ k ∈ s)
    (ε : K → ℤ) (w : T → M) :
    ∏ k, w (φ k) ^ ε k = ∏ ψ ∈ s, w ψ ^ (∑ k, if φ k = ψ then ε k else 0) := by
  have h : ∀ ψ, w ψ ^ (∑ k, if φ k = ψ then ε k else 0) = ∏ k, if φ k = ψ then w ψ ^ ε k else 1 := fun ψ => by
    have hz : ∀ t : Finset K, ∀ a : K → ℤ, w ψ ^ (∑ k ∈ t, a k) = ∏ k ∈ t, w ψ ^ a k := fun t a => by
      induction t using Finset.induction_on with
      | empty => simp
      | insert b t hb ih => rw [Finset.sum_insert hb, Finset.prod_insert hb, zpow_add, ih]
    rw [hz]
    refine Finset.prod_congr rfl fun k _ => ?_
    split_ifs <;> simp
  simp only [h]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_ite_eq, if_pos (hs k)]


open scoped Classical in
theorem prod_zpow_eq {M T K K' : Type*} [CommGroup M] [Fintype K] [Fintype K'] (φ : K → T) (ε : K → ℤ)
    (φ' : K' → T) (ε' : K' → ℤ) (u : K → M) (u' : K' → M)
    (h₁ : ∀ k l, φ k = φ l → u k = u l) (h₂ : ∀ k l, φ' k = φ' l → u' k = u' l)
    (h₃ : ∀ k l, φ k = φ' l → u k = u' l)
    (hs : ∀ ψ, (∑ k, if φ k = ψ then ε k else 0) = ∑ k', if φ' k' = ψ then ε' k' else 0) :
    ∏ k, u k ^ ε k = ∏ k, u' k ^ ε' k := by
  let w : T → M := fun ψ => if h : ∃ k, φ k = ψ then u h.choose else if h' : ∃ k, φ' k = ψ then u' h'.choose else 1
  have hw : ∀ k, u k = w (φ k) := fun k => by
    have h : ∃ l, φ l = φ k := ⟨k, rfl⟩
    simp only [w, dif_pos h]
    exact h₁ _ _ h.choose_spec.symm
  have hw' : ∀ k, u' k = w (φ' k) := fun k => by
    by_cases h : ∃ l, φ l = φ' k
    · simp only [w, dif_pos h]
      exact (h₃ _ _ h.choose_spec).symm
    · have h' : ∃ l, φ' l = φ' k := ⟨k, rfl⟩
      simp only [w, dif_neg h, dif_pos h']
      exact h₂ _ _ h'.choose_spec.symm
  simp only [hw, hw']
  rw [prod_zpow_fiber (Finset.univ.image φ ∪ Finset.univ.image φ') φ (fun k => by simp) ε w,
    prod_zpow_fiber (Finset.univ.image φ ∪ Finset.univ.image φ') φ' (fun k => by simp) ε' w]
  simp only [hs]

section Frame

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)


set_option backward.isDefEq.respectTransparency false in
theorem origin_mem {n m : ℕ} {ψ : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left}
    {Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)} (h : Φ.JetMap m ψ Λ) {U : A.left.Opens}
    (p : Sp (Jet ℂ (Fin n × Fin g) m)) (hp : ψ p ∈ U) : ⊤ ≤ (Φ.e 0).left ⁻¹ᵁ U := by
  obtain ⟨hol, rfl⟩ := h
  rw [Scheme.Hom.comp_apply, jet_point_eq (K := ℂ) (J := Fin 1 × Fin (n * g)) (m := m)
      (spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) p),
    jetPt_closedPoint] at hp
  have hc : colsOf n g 0 = 0 := rfl
  rw [hc, map_zero] at hp
  exact top_le_of_mem hp

theorem fr_analyticAt (j : L.L.ι) (h : ⊤ ≤ (Φ.e 0).left ⁻¹ᵁ L.L.U j) : AnalyticAt ℂ (Φ.fr j) 0 :=
  GlobalTheory.SCV.analyticAt_of_differentiableOn (Φ.fr_hol j) ((Φ.hol (L.L.U j) 0).1.mem_nhds h)

end Frame


set_option backward.isDefEq.respectTransparency false in
theorem corr_of_jetRd : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), Φ.Imm → ∀ (n m : ℕ) (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε : K → ℤ) (τ : LB.Gen (LB.LinComb L.L φ ε)) (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (φ' : K' → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε' : K' → ℤ) (τ' : LB.Gen (LB.LinComb L.L φ' ε')) (Λ' : K' → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), Φ.JetRd m φ ε τ Λ → Φ.JetRd m φ' ε' τ' Λ' → LB.SameSum φ ε φ' ε' → LB.Gen.Corr L.L φ ε φ' ε' τ τ' := by
  intro S A _ _ L x0 g Φ hI n m K K' _ _ φ ε τ Λ φ' ε' τ' Λ' h h' hs j j' c c' cc
  by_cases hW : ∃ p, p ∈ LB.wchart L.L φ j ⊓ LB.wchart L.L φ' j'
  · obtain ⟨p, hp⟩ := hW
    have hT : ⊤ ≤ LB.wchart L.L φ j ⊓ LB.wchart L.L φ' j' := fun q _ => by
      have e1 := jet_point_eq (K := ℂ) (J := Fin n × Fin g) (m := m) p
      have e2 := jet_point_eq (K := ℂ) (J := Fin n × Fin g) (m := m) q
      rw [e2, ← e1]
      exact hp
    have o : ∀ k, ⊤ ≤ (Φ.e 0).left ⁻¹ᵁ L.L.U (j k) := fun k =>
      origin_mem Φ (h.1 k) p (LB.wchart_le L.L φ j k hp.1)
    have o' : ∀ k, ⊤ ≤ (Φ.e 0).left ⁻¹ᵁ L.L.U (j' k) := fun k =>
      origin_mem Φ (h'.1 k) p (LB.wchart_le L.L φ' j' k hp.2)
    obtain ⟨u, hu, hP⟩ := jetN_prod_zpow m (fun k => Φ.fr (j k)) (fun k => fr_analyticAt Φ _ (o k))
      (fun k => Φ.fr_ne _ _ (o k)) Λ ε
    obtain ⟨u', hu', hP'⟩ := jetN_prod_zpow m (fun k => Φ.fr (j' k)) (fun k => fr_analyticAt Φ _ (o' k))
      (fun k => Φ.fr_ne _ _ (o' k)) Λ' ε'
    have hE : ∏ k, u k ^ ε k = ∏ k, u' k ^ ε' k := by
      refine prod_zpow_eq φ ε φ' ε' u u' (fun k l e => Units.ext ?_) (fun k l e => Units.ext ?_)
        (fun k l e => Units.ext ?_) hs
      · rw [hu, hu, c k l e]
        exact GlobalTheory.AnVal.JetUniq.jet_uniq S A L x0 g Φ hI n m (φ l) _ _ (e ▸ h.1 k) (h.1 l) _
      · rw [hu', hu', c' k l e]
        exact GlobalTheory.AnVal.JetUniq.jet_uniq S A L x0 g Φ hI n m (φ' l) _ _ (e ▸ h'.1 k) (h'.1 l) _
      · rw [hu, hu', cc k l e]
        exact GlobalTheory.AnVal.JetUniq.jet_uniq S A L x0 g Φ hI n m (φ' l) _ _ (e ▸ h.1 k) (h'.1 l) _
    have r := h.2 j (hT.trans inf_le_left)
    have r' := h'.2 j' (hT.trans inf_le_right)
    rw [hP, hE, ← hP', ← r'] at r
    apply Units.ext
    have r2 := congrArg ((Sp (Jet ℂ (Fin n × Fin g) m)).presheaf.map
      (homOfLE (le_top : LB.wchart L.L φ j ⊓ LB.wchart L.L φ' j' ≤ ⊤)).op).hom r
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp] at r2
    exact r2
  · have hB : LB.wchart L.L φ j ⊓ LB.wchart L.L φ' j' = ⊥ := by
      rw [eq_bot_iff]
      exact fun p hp => (hW ⟨p, hp⟩).elim
    have : Subsingleton Γ(Sp (Jet ℂ (Fin n × Fin g) m), LB.wchart L.L φ j ⊓ LB.wchart L.L φ' j') := by
      rw [hB]; infer_instance
    exact Units.ext (Subsingleton.elim _ _)

end GlobalTheory.AnVal.JetCorr
end
end

section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GalTw

theorem _root_.GlobalTheory.T.shortSeriesValue_twisted_eq_conjugate_value : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (ta : c.F ≃+* c.F) (h : Fixes c ta), ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (b : c.F) (N : ℕ) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : Tw ta S), ShortValAt Xo c nab w Λ b N P (twPt h y) v → ShortValAt Xo c nab (fun q => ta (w q)) Λ (ta b) N (MvPolynomial.map (ta : c.F →+* c.F) P) y v.val := by
  first | exact @GlobalTheory.GalTw.shortValAt_conj | exact GlobalTheory.GalTw.shortValAt_conj | (intros; apply GlobalTheory.GalTw.shortValAt_conj <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaBase

open GlobalTheory.ThetaCoord GlobalTheory.VVRank

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem mk_eq_zero_iff (k : ℕ) (m : Dw.La) :
    (Submodule.Quotient.mk m : LatMod Dw k) = 0 ↔ ∃ m' : Dw.La, k • m' = m := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and, Nat.cast_smul_eq_nsmul]

theorem exists_shift {R : ℕ} (hR : R ≠ 0) (q : LatMod Dw (R ^ 4)) (hq : R • q = 0) :
    ∃ u : LatMod Dw R, (Submodule.Quotient.mk (R ^ 3 • qRep u) : LatMod Dw (R ^ 4)) = q := by
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨m', hm⟩ := (mk_eq_zero_iff (R ^ 4) (R • m)).1 hq
  have e : R ^ 3 • m' = m := by
    have h : R • R ^ 3 • m' = R • m := by rw [← hm, ← mul_nsmul', ← pow_succ']
    refine Dw.unimod.1 (LinearMap.ext fun v => nsmul_right_injective hR ?_)
    have := congrArg (fun t => Dw.EF t v) h
    simpa only [map_nsmul, LinearMap.smul_apply] using this
  refine ⟨Submodule.Quotient.mk m', ?_⟩
  have h : (Submodule.Quotient.mk (qRep (Submodule.Quotient.mk m' : LatMod Dw R)) : LatMod Dw R) =
      Submodule.Quotient.mk m' := Classical.choose_spec (Submodule.Quotient.mk_surjective _ _)
  rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub] at h ⊢
  obtain ⟨d, hd⟩ := (mk_eq_zero_iff R _).1 h
  refine (mk_eq_zero_iff _ _).2 ⟨d, ?_⟩
  rw [← e, ← smul_sub, ← hd, ← mul_nsmul', ← pow_succ]

variable (Xo : Moduli Dw l) (c : Coeff l)

theorem gen_ne_zero {K : Type} [CommRing K] [Nontrivial K] [Algebra c.F K] (y : FrPt Xo c K) :
    (SecM.ofSec Xo.univ.t.G y.s : SecM Xo.univ.t.G Xo.univ.t.PP.L 1 (Over.mk y.x)) ≠ 0 := fun h => by
  have h₀ : ∀ i, y.s.f i = 0 := fun i => congrFun (congrArg Subtype.val h) i
  exact zero_ne_one ((y.gen y.s).unique (y₁ := 0) (y₂ := 1) (fun i => by rw [h₀, MulZeroClass.mul_zero])
    (fun i => by rw [h₀, MulZeroClass.mul_zero]))

theorem exists_nullVal_ne_zero (hL : Laws) {K : Type} [Field K] [IsAlgClosed K] [Algebra c.F K] (y : FrPt Xo c K)
    (N : ℕ) {n : ℕ} (hn : 2 ≤ n) (a : ptO Xo y.x ⟶ Xo.univ.t.G) :
    ∃ z : ptO Xo y.x ⟶ Xo.univ.t.G, z ^ n = 1 ∧
      ∀ p w, IsNullVal Xo c N y p w → p ^ N = a * z → w ≠ 0 := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
  have hK : (n : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨z, hz, hu⟩ := UT.ExactTerm.exists_good_point hL.goodPt hL.polBaseChange (UnivPol.pol Xo) y.x hn hK y.s
    (gen_ne_zero Xo c y) a
  refine ⟨z, hz, ?_⟩
  rintro p w ⟨F, ⟨t', α₀, α, s₁, U, -, rfl, -, -, -, hs₁, hU, hF⟩, hw⟩ hp h₀
  let o : (Over.mk y.x).left := IsLocalRing.closedPoint K
  choose J hJ using fun χ : (Over.mk y.x).left ⟶ Xo.univ.t.G.left => exists_chart Xo.univ.t.PP.isLB (χ o)
  replace hJ : Good Xo.univ.t.PP.L o J := hJ
  have b₁ := sv_act hU.pt_eq hF (𝟙 _) hJ 1
  have b₂ := sv_mulPull hs₁ (𝟙 _) hJ t'
  have b₃ := sv_of_isValueAt hw (𝟙 _) hJ
  rw [Category.id_comp, _root_.mul_one] at b₁
  rw [Category.id_comp] at b₃
  rw [b₃, b₂, hp, h₀, map_zero, UT.ExactTerm.gs_zero' _ _ ⊤ trivial, MulZeroClass.zero_mul] at b₁
  exact ((Units.isUnit _).mul ((Units.isUnit _).mul (hu o J hJ))).ne_zero b₁.symm

end GlobalTheory.EtaBase

namespace GlobalTheory

open GlobalTheory.EtaBase

theorem exists_shift_nullVal_ne_zero : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : ℕ), Odd R → 1 < R → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra c.F K] (y : FrPt Xo c K) (ev : LatMod Dw (R ^ 4) → (ptO Xo y.x ⟶ Xo.univ.t.G)) (w : LatMod Dw (R ^ 4) → K), IsFullLev Xo (R ^ 4) y.x ev → (∀ q, IsNullVal Xo c (R ^ 2) y (ev q) (w q)) → ∀ (n : ℕ) (x₀ : Fin n → Dw.La) (g : LevGrp Dw (R ^ 4)), ∃ u : Fin n → LatMod Dw R, ∀ b, w (g (shiftFam R x₀ u b)) ≠ 0 := by
  intro hL E _ _ _ H Dw l Xo c R _ hR K _ _ _ y ev w hev hw n x₀ g
  have hR₀ : R ≠ 0 := by omega
  have e₀ : ev 0 = 1 := by
    have := hev.1 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have es : ∀ (m : ℕ) q, ev (m • q) = ev q ^ m := fun m q => by
    induction m with
    | zero => rw [zero_smul, e₀, pow_zero]
    | succ m ih => rw [succ_nsmul, hev.1, ih, pow_succ]
  have sur := ((T.fullLinearLevel_cover_baseChange_torsor hL E H Dw l Xo (R ^ 4) (by positivity)).2.2.1 K y.x ev hev).1
  have key : ∀ x : Dw.La, ∃ u : LatMod Dw R,
      w (g (Submodule.Quotient.mk (x + R • qRep u))) ≠ 0 := fun x => by
    obtain ⟨z, hz, h⟩ := exists_nullVal_ne_zero Xo c hL y (R ^ 2) hR (ev (g (Submodule.Quotient.mk x)) ^ R ^ 2)
    obtain ⟨q, rfl⟩ := sur z (by rw [pow_succ', pow_mul, hz, one_pow])
    have hq : R • q = 0 := hev.2.2 K (RingHom.id K) _ _ (by rw [es, hz, e₀])
    obtain ⟨u, hu⟩ := exists_shift hR₀ (g.symm q) (by rw [← map_nsmul, hq, map_zero])
    refine ⟨u, h _ _ (hw _) ?_⟩
    rw [← es, ← es, ← hev.1, ← g.apply_symm_apply q, ← hu, ← map_nsmul, ← map_nsmul, ← map_add (f := _)]
    congr 2
    show (Submodule.Quotient.mk (R ^ 2 • (x + R • qRep u)) : LatMod Dw (R ^ 4)) =
      Submodule.Quotient.mk (R ^ 2 • x + R ^ 3 • qRep u)
    rw [smul_add, ← mul_nsmul', ← pow_succ]
  choose u hu using key
  exact ⟨fun b => u (x₀ b), fun b => hu (x₀ b)⟩

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem exists_wchart_complexPt {X Z : Scheme.{0}} (L : LB X) (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Z ⟶ X)) (q : Sp ℂ ⟶ Z) : ∃ j : K → L.ι, ⊤ ≤ q ⁻¹ᵁ LB.wchart L φ j := by
  obtain ⟨hcov, -, -⟩ := hL
  have hmem : ∀ y : X, ∃ i, y ∈ L.U i := by
    intro y
    have hy : y ∈ (⨆ i, L.U i) := by rw [hcov]; trivial
    exact (TopologicalSpace.Opens.mem_iSup).1 hy
  have hsub : Subsingleton (Sp ℂ) := by
    change Subsingleton (PrimeSpectrum ℂ)
    infer_instance
  have p0 : Sp ℂ := by
    change PrimeSpectrum ℂ
    exact default
  choose j hj using fun k => hmem (φ k (q p0))
  refine ⟨j, fun y _ => ?_⟩
  rw [Subsingleton.elim y p0]
  show q p0 ∈ L.wchart φ j
  unfold LB.wchart
  exact Set.mem_iInter.2 fun k => hj k

theorem AnFr.rd_of_isActOf : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (k : ℤ) (U : ThetaGrp A L.L k (Over.mk x0)) (x : Fin g → ℂ) (c : ℂ) (s s' : LB.Sec (LPow A L.L k (Over.mk x0))) (θ : (Fin g → ℂ) → ℂ), Φ.ThConst k U x c → IsActOf A L.L k U s s' → Φ.Rd k s θ → Φ.Rd k s' (fun z => c * fock Φ.Hm k x θ z) := by
  intro S A _ _ L x0 g Φ k U x c s s' θ hc ha hr
  obtain ⟨-, hz⟩ := hc
  have hfst : translT A U.pt ≫ fst (Over.mk x0) A = fst (Over.mk x0) A := by
    unfold translT
    exact lift_fst _ _
  have hsnd : translT A U.pt ≫ snd (Over.mk x0) A = translPt A U.pt := by
    unfold translT
    exact lift_snd _ _
  have htw : IsTwistPull A L.L (translT A U.pt) (translPt A U.pt) hsnd k k U.φ s s' := by
    unfold IsActOf at ha
    exact ha
  have hcond : ∀ z, (ptSecT A (Φ.e z)).left ≫ (translPt A U.pt).left = (Φ.e (x + z)).left ∧
      ∃ j : Fin 2 → L.L.ι, ⊤ ≤ (ptSecT A (Φ.e z)).left ⁻¹ᵁ
          LB.wchart L.L ![(snd (Over.mk x0) A).left, (translPt A U.pt).left] j ∧
        valAt' (ptSecT A (Φ.e z)).left
            (LB.wchart L.L ![(snd (Over.mk x0) A).left, (translPt A U.pt).left] j) (U.φ.s j).val =
          c * fock Φ.Hm k x (fun _ => 1) z * (Φ.fr (j 0) z ^ k * Φ.fr (j 1) (x + z) ^ (-k)) := by
    intro z
    obtain ⟨hmaps, hval⟩ := hz z
    refine ⟨by simpa using hmaps 1, ?_⟩
    obtain ⟨j, hj⟩ := exists_wchart_complexPt L.L L.isLB
      ![(snd (Over.mk x0) A).left, (translPt A U.pt).left] (ptSecT A (Φ.e z)).left
    refine ⟨j, hj, ?_⟩
    rw [hval j hj, Fin.prod_univ_two]
    simp
  have key := GlobalTheory.T.reading_twisted_pullback S A L x0 g Φ (translT A U.pt) (translPt A U.pt) hsnd k k U.φ s s' θ
    (fun z => x + z) (fun z => c * fock Φ.Hm k x (fun _ => 1) z) hfst htw hr hcond
  have hfun : (fun z => c * fock Φ.Hm k x (fun _ => 1) z * θ (x + z)) = fun z => c * fock Φ.Hm k x θ z := by
    funext z
    simp only [fock]
    rw [add_comm x z]
    ring
  rw [← hfun]
  exact key

end GlobalTheory.AnVal
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cmFrame_jetPoints_are_exponential_jets : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ (n m : ℕ), (∀ i : Fin n, Φ.toAnFr.JetMap m (jpt y g Φ.jx m i).left (LinearMap.proj i)) ∧ Φ.toAnFr.JetMap m (1 : jO y g m n ⟶ Xo.univ.t.G).left 0 ∧ (∀ (a b : jO y g m n ⟶ Xo.univ.t.G) (Λ Λ' : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), Φ.toAnFr.JetMap m a.left Λ → Φ.toAnFr.JetMap m b.left Λ' → Φ.toAnFr.JetMap m (a * b).left (Λ + Λ') ∧ ∃ hq : IsHolFam (fun v : Fin (n * g) → ℂ => (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left), (lift a b).left = spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫ jetPt _ hq m) ∧ (∀ (a : jO y g m n ⟶ Xo.univ.t.G) (Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (α : 𝓞 E), Φ.toAnFr.JetMap m a.left Λ → Φ.toAnFr.JetMap m (a ≫ Xo.univ.t.act.act α).left (tyAct ty α ∘ₗ Λ)) ∧ Φ.toAnFr.JetMap (n := 1) m (Φ.jx m).left (LinearMap.proj 0) := by
  first | exact @GlobalTheory.AnVal.jetPts_jetMap | exact GlobalTheory.AnVal.jetPts_jetMap | (intros; apply GlobalTheory.AnVal.jetPts_jetMap <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaConstant_pow_eq_one_of_power_trivial : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (k : ℤ) (n : ℕ) (U : ThetaGrp A L.L k (Over.mk x0)) (x : Fin g → ℂ) (c : ℂ), Φ.ThConst k U x c → (n : ℂ) • x ∈ Φ.lat → LB.Gen.Corr L.L _ _ _ _ (powGen A L.L k U n) (LB.oneGen L.L) → c ^ n * Φ.χ ((n : ℂ) • x) ^ k = 1 := by
  first | exact @GlobalTheory.AnValThPow.thConst_pow | exact GlobalTheory.AnValThPow.thConst_pow | (intros; apply GlobalTheory.AnValThPow.thConst_pow <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_thetaConstant_of_thetaGroup : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (k : ℤ) (U : ThetaGrp A L.L k (Over.mk x0)) (x : Fin g → ℂ), U.pt = Φ.e x → ∃ c : ℂ, c ≠ 0 ∧ Φ.ThConst k U x c := by
  first | exact @GlobalTheory.AnVal.exists_thConst | exact GlobalTheory.AnVal.exists_thConst | (intros; apply GlobalTheory.AnVal.exists_thConst <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cmFrame_exponential_jets_isChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), IsChart y g (anFB ty).G.F (anFB ty).A.act (anUvec el) Φ.jx := by
  first | exact @GlobalTheory.AnVal.anPt_isChart | exact GlobalTheory.AnVal.anPt_isChart | (intros; apply GlobalTheory.AnVal.anPt_isChart <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_faithfullyFlat_split_isotropicGroup : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x0 : Sp S ⟶ Xo.X) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G)), φ.FaithfullyFlat ∧ (∀ i, InZh Xo Λ N (z i)) ∧ GeoInj Xo (spMap φ ≫ x0) z := by
  first | exact @GlobalTheory.exists_faithfullyFlat_split_Zh | exact GlobalTheory.exists_faithfullyFlat_split_Zh | (intros; apply GlobalTheory.exists_faithfullyFlat_split_Zh <;> assumption)
end
