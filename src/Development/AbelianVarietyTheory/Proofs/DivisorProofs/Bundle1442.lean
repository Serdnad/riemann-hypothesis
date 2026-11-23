module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1203
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1238
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1354
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianMultiplicationModelNonsplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKernelSignEqEtaGramDet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1356
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1357
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1355

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

theorem _root_.GlobalTheory.T.topFormOrder_rationalPullback_of_essentiallyEtale : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [LocallyOfFiniteType p], topologicalKrullDim W = n → ∀ (E : DivOver p) (E' : DivOver (f ≫ p)) (h : ∀ x ∈ E.ring, functionFieldMap f x ∈ E'.ring), ((functionFieldMap f).restrict E.ring E'.ring h).FormallyEtale → (∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g) → ∀ η : RatForms p n, η ≠ 0 → (fun ω => @dite ℤ (∃ a, E'.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (GlobalTheory.EtaleKlt.ratPull p f n η) = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η := by
  first | exact @GlobalTheory.EtaleKlt.formOrd_ratPull | exact GlobalTheory.EtaleKlt.formOrd_ratPull | (intros; apply GlobalTheory.EtaleKlt.formOrd_ratPull <;> assumption)
end

section

open Filter GlobalTheory.BCT
open scoped Classical

theorem _root_.GlobalTheory.T.twistedOrbitalIntegralSummand_goodPlace_indicator : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (KH : Subgroup H) (δ : H), δ ∈ KH → cptPart (twCent (MonoidHom.id H) δ) ≤ KH → (∀ g : H, g⁻¹ * δ * g ∈ KH → ∃ t ∈ twCent (MonoidHom.id H) δ, t⁻¹ * g ∈ KH) → ∀ x : H, GlobalTheory.TwOrbConj.summand (MonoidHom.id H) KH δ ((KH : Set H).indicator 1) x = if ∃ t ∈ twCent (MonoidHom.id H) δ, ∃ k ∈ KH, x = t * k then 1 else 0 := by
  first | exact @GlobalTheory.TwOrbGood.summand_goodplace | exact GlobalTheory.TwOrbGood.summand_goodplace | (intros; apply GlobalTheory.TwOrbGood.summand_goodplace <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.exists_ne_zero_of_twistedOrbitalPointTerm_ne_zero : ∀ {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (y : G), GlobalTheory.EulerAbs.twTerm θ K δ f y ≠ 0 → ∃ k ∈ K, f ((y * k)⁻¹ * δ * θ (y * k)) ≠ 0 := by
  first | exact @GlobalTheory.EulerAbs.exists_ne_zero_of_twTerm_ne_zero | exact GlobalTheory.EulerAbs.exists_ne_zero_of_twTerm_ne_zero | (intros; apply GlobalTheory.EulerAbs.exists_ne_zero_of_twTerm_ne_zero <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.twistedOrbitalIntegralPointTerm_one_unramified : ∀ {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G), (∀ k ∈ K, θ k ∈ K) → δ ∈ K → cptPart (twCent θ δ) ≤ K → GlobalTheory.EulerAbs.twTerm θ K δ ((K : Set G).indicator 1) 1 = 1 := by
  first | exact @GlobalTheory.EulerAbs.twTerm_one_eq_one | exact GlobalTheory.EulerAbs.twTerm_one_eq_one | (intros; apply GlobalTheory.EulerAbs.twTerm_one_eq_one <;> assumption)
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

noncomputable section

namespace GlobalTheory.KapOrb.CongNorm

variable {E : Type} [Field E] [NumberField E]

theorem val_mul_mul_le {R Γ : Type} [CommRing R] [LinearOrderedCommMonoidWithZero Γ] (v : Valuation R Γ) {n : ℕ}
    (A X B : Matrix (Fin n) (Fin n) R) (c : Γ) (hA : ∀ i j, v (A i j) ≤ 1) (hB : ∀ i j, v (B i j) ≤ 1)
    (hX : ∀ i j, v (X i j) ≤ c) (i j : Fin n) : v ((A * X * B) i j) ≤ c := by
  rw [Matrix.mul_apply]
  refine v.map_sum_le fun l _ => ?_
  rw [Matrix.mul_apply, v.map_mul]
  have h1 : v (∑ m, A i m * X m l) ≤ c := v.map_sum_le fun m _ => by
    rw [v.map_mul]
    calc v (A i m) * v (X m l) ≤ 1 * c := mul_le_mul' (hA i m) (hX m l)
      _ = c := one_mul c
  calc v (∑ m, A i m * X m l) * v (B l j) ≤ c * 1 := mul_le_mul' h1 (hB l j)
    _ = c := mul_one c

theorem val_le_one_of_mem_KGL (w : Pl E) {n : ℕ} {g : GLw n w} (hg : g ∈ GlobalTheory.LFun.KGL w (n := n)) (i j : Fin n) :
    Valued.v (g.val i j) ≤ 1 := by
  obtain ⟨y, rfl⟩ := hg
  have : ((Formalism.UG.bc (n := Fin n) (Ov E w).subtype y).val i j) = ((y.val i j : Ov E w) : w.adicCompletion E) := rfl
  rw [this]
  exact (HeightOneSpectrum.mem_adicCompletionIntegers (K := E) (v := w)).1 (y.val i j).2

theorem conj_bound (w : Pl E) {n : ℕ} (c : WithZero (Multiplicative ℤ)) {a x : GLw n w} (ha : a ∈ GlobalTheory.LFun.KGL w (n := n))
    (hx : ∀ i j, Valued.v ((x.val - 1) i j) ≤ c) (i j : Fin n) :
    Valued.v (((a⁻¹ * x * a).val - 1) i j) ≤ c := by
  have e : (a⁻¹ * x * a).val - 1 = (a⁻¹).val * (x.val - 1) * a.val := by
    have h1 : (a⁻¹).val * a.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1, Units.val_mul, Units.val_mul]
  rw [e]
  exact val_mul_mul_le Valued.v _ _ _ c (val_le_one_of_mem_KGL w (inv_mem ha))
    (val_le_one_of_mem_KGL w ha) hx i j

end GlobalTheory.KapOrb.CongNorm

namespace GlobalTheory.KapOrb

theorem conj_mem_congSet_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n m : ℕ)
    (h k : GLw n w), k ∈ GlobalTheory.LFun.KGL w (n := n) → (k⁻¹ * h * k ∈ congSet w n m ↔ h ∈ congSet w n m) := by
  intro E _ _ _ w n m h k hk
  have hmem : k⁻¹ * h * k ∈ GlobalTheory.LFun.KGL w (n := n) ↔ h ∈ GlobalTheory.LFun.KGL w (n := n) := by
    rw [Subgroup.mul_mem_cancel_right _ hk, Subgroup.mul_mem_cancel_left _ (inv_mem hk)]
  have hb : ∀ g : GLw n w, (∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤
      WithZero.exp (-(m : ℤ))) ↔ ∀ i j, Valued.v ((g.val - 1) i j) ≤ WithZero.exp (-(m : ℤ)) := fun g => by
    simp only [Matrix.sub_apply]
  simp only [congSet, Set.mem_ofPred_eq, hb, hmem]
  refine and_congr_right fun _ => ⟨fun H => ?_, fun H => CongNorm.conj_bound w _ hk H⟩
  have e : h = k⁻¹⁻¹ * (k⁻¹ * h * k) * k⁻¹ := by group
  rw [e]
  exact CongNorm.conj_bound w _ (inv_mem hk) H

end GlobalTheory.KapOrb
end
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

theorem _root_.GlobalTheory.T.hermitianModels_conj_unitary_differ_by_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (n : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K) (u x x' : B.A), Q.Separable → Fits w e B Q u → ∀ γ y : GLw n w, y ∈ UL n w → IsModel w e B u x γ → IsModel w e B u x' (y⁻¹ * γ * y) → ∃ c : B.Aˣ, x' = x * ((c : B.A) * B.σ (c : B.A)) := by
  first | exact @GlobalTheory.KapLat.model_conj_norm | exact GlobalTheory.KapLat.model_conj_norm | (intros; apply GlobalTheory.KapLat.model_conj_norm <;> assumption)
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

theorem _root_.GlobalTheory.T.exists_hermitianMultiplicationModel_nonsplit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (n : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K) (u : B.A), Q.Separable → Fits w e B Q u → ∀ γ : GLw n w, γ ∈ UL n w → γ.val.charpoly = Q → ∃ x : B.A, B.σ x = x ∧ IsUnit x ∧ IsModel w e B u x γ := by
  first | exact @GlobalTheory.KapLat.ExModel.exists_isModel | exact GlobalTheory.KapLat.ExModel.exists_isModel | (intros; apply GlobalTheory.KapLat.ExModel.exists_isModel <;> assumption)
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

theorem _root_.GlobalTheory.T.inertPlace_kernelSign_eq_eta_gramDet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (n : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K) (u₁ : B₁.A) (u₂ : B₂.A), (Q₁ * Q₂).Separable → Fits w e B₁ Q₁ u₁ → Fits w e B₂ Q₂ u₂ → ∀ (x : (B₁.prod B₂).A) (γ : GLw n w), IsModel w e (B₁.prod B₂) ((u₁, u₂) : B₁.A × B₂.A) x γ → kapSign n w Q₁ γ = ((K.eta (B₁.gramDet x.1) : ℚ) : ℂ) := by
  first | exact @GlobalTheory.KapLat.kapSign_eq_eta_gramDet | exact GlobalTheory.KapLat.kapSign_eq_eta_gramDet | (intros; apply GlobalTheory.KapLat.kapSign_eq_eta_gramDet <;> assumption)
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

theorem _root_.GlobalTheory.T.latticeSpannedByGLColumns_eq_iff_GLint_coset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), (∀ g g' : GLw m w, GlobalTheory.TwLat.lat e b g = GlobalTheory.TwLat.lat e b g' ↔ g⁻¹ * g' ∈ GlobalTheory.LFun.KGL w (n := m)) ∧ ∀ g : GLw m w, GlobalTheory.UnitLemma.IsLat K.O K.E (GlobalTheory.TwLat.lat e b g) := by
  first | exact @GlobalTheory.TwLatCoset.lat_coset | exact GlobalTheory.TwLatCoset.lat_coset | (intros; apply GlobalTheory.TwLatCoset.lat_coset <;> assumption)
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

theorem _root_.GlobalTheory.T.traceFormGram_asymmetry_forces_beta_relation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A) (u β : B.A), (Algebra.traceForm K.E B.A).Nondegenerate → IsUnit (GlobalTheory.TwLat.gram e b β) → (cj w).mapMatrix (GlobalTheory.TwLat.gram e b β) = (-1 : w.adicCompletion E) ^ (m - 1) • ((GlobalTheory.TwLat.gram e b β)ᵀ * GlobalTheory.TwLat.mulMat e b u) → B.σ β = β * ((-1) ^ (m - 1) * u) ∧ IsUnit β := by
  first | exact @GlobalTheory.TwLat.betaSym | exact GlobalTheory.TwLat.betaSym | (intros; apply GlobalTheory.TwLat.betaSym <;> assumption)
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

theorem _root_.GlobalTheory.T.exists_GL_completion_lattice_eq_columns : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ L : Submodule K.O B.A, GlobalTheory.UnitLemma.IsLat K.O K.E L → ∃ g : GLw m w, GlobalTheory.TwLat.lat e b g = L := by
  first | exact @GlobalTheory.TwLat.exists_GLw_lat_eq | exact GlobalTheory.TwLat.exists_GLw_lat_eq | (intros; apply GlobalTheory.TwLat.exists_GLw_lat_eq <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TwOrbLat

theorem exists_lat_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ)
    (e : K.E ≃+* w.adicCompletion E) (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (b : Module.Basis (Fin a) K.E B.A)
    (L : Submodule K.O B.A), GlobalTheory.UnitLemma.IsLat K.O K.E L → ∃ q : GLw a w, GlobalTheory.TwLat.lat e b q = L := by
  intro E _ _ _ w K e a B b L hL
  obtain ⟨hfg, hspan⟩ := hL
  haveI : Module.Finite K.O L := Module.Finite.iff_fg.mpr hfg
  haveI : NoZeroSMulDivisors K.O B.A := ⟨fun {r x} h => by
    rw [← algebraMap_smul K.E r x] at h
    rcases smul_eq_zero.mp h with h | h
    · left; exact (IsFractionRing.injective K.O K.E) (by simpa using h)
    · right; exact h⟩
  haveI : Module.Free K.O L := Module.free_of_finite_type_torsion_free'
  let y := Module.Free.chooseBasis K.O L
  let v : Module.Free.ChooseBasisIndex K.O L → B.A := fun i => (y i : B.A)
  have hli : LinearIndependent K.O v := y.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
  have hliE : LinearIndependent K.E v := (LinearIndependent.iff_fractionRing K.O K.E).mp hli
  have hLv : Submodule.span K.O (Set.range v) = L := by
    have : Set.range v = L.subtype '' Set.range y := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, y.span_eq, Submodule.map_subtype_top]
  have hspE : Submodule.span K.E (Set.range v) = ⊤ := by
    rw [← Submodule.span_span_of_tower K.O K.E, hLv]; exact hspan
  let c := Module.Basis.mk hliE hspE.ge
  let c' := c.reindex (c.indexEquiv b)
  let U : (Matrix (Fin a) (Fin a) K.E)ˣ :=
    ⟨b.toMatrix c', c'.toMatrix b, b.toMatrix_mul_toMatrix_flip c', c'.toMatrix_mul_toMatrix_flip b⟩
  refine ⟨Units.map (e.toRingHom.mapMatrix : Matrix (Fin a) (Fin a) K.E →+* _).toMonoidHom U, ?_⟩
  rw [latOf_eq, ← hLv]
  have hcol : ∀ j, (ofCrd e b fun i =>
      (Units.map (e.toRingHom.mapMatrix : Matrix (Fin a) (Fin a) K.E →+* _).toMonoidHom U).val i j) = c' j := by
    intro j
    rw [← ofCrd_crd e b (c' j)]
    congr 1
  simp only [hcol]
  congr 1
  ext x
  simp only [Set.mem_range]
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨(c.indexEquiv b).symm j, ?_⟩
    simp [c', c, v]
  · rintro ⟨i, rfl⟩
    refine ⟨c.indexEquiv b i, ?_⟩
    simp [c', c, v]

end GlobalTheory.TwOrbLat
end
end
