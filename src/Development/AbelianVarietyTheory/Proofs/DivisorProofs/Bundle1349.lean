module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1214
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle122
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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

@[expose] public section

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.RatDarboux

theorem exists_rat_matrix {F R V W ι : Type} [Field F] [CommRing R] [Nontrivial R] [Algebra F R] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] [AddCommGroup W] [Module R W] [Fintype ι] [DecidableEq ι]
    (j : V →+ W) (hj : ∀ (c : F) x, j (c • x) = algebraMap F R c • j x) (hinj : Function.Injective j)
    (hc : Module.finrank F V = Fintype.card ι) (e₀ e₂ : W ≃ₗ[R] (ι → R))
    (h₀ : ∀ x, ∃ u : ι → F, e₀ (j x) = fun i => algebraMap F R (u i))
    (h₂ : ∀ x, ∃ u : ι → F, e₂ (j x) = fun i => algebraMap F R (u i)) :
    ∃ g : Matrix ι ι F, ∀ w, e₂ w = g.map (algebraMap F R) *ᵥ e₀ w := by
  classical
  have hφ : Function.Injective (algebraMap F R) := (algebraMap F R).injective
  have hvec : ∀ a b : ι → F, (fun i => algebraMap F R (a i)) = (fun i => algebraMap F R (b i)) → a = b := by
    intro a b h
    funext i
    exact hφ (congrFun h i)

  have lin : ∀ (e : W ≃ₗ[R] (ι → R)) (u : V → ι → F), (∀ x, e (j x) = fun i => algebraMap F R (u x i)) →
      ∃ U : V →ₗ[F] (ι → F), ∀ x, U x = u x := by
    intro e u hu
    refine ⟨{ toFun := u, map_add' := ?_, map_smul' := ?_ }, fun x => rfl⟩
    · intro x y
      apply hvec
      rw [← hu, map_add (f := _), map_add (f := _), hu, hu]
      funext i
      simp
    · intro c x
      apply hvec
      rw [← hu, hj, map_smul, hu]
      funext i
      simp
  choose u₀ hu₀ using h₀
  choose u₂ hu₂ using h₂
  obtain ⟨U₀, hU₀⟩ := lin e₀ u₀ hu₀
  obtain ⟨U₂, hU₂⟩ := lin e₂ u₂ hu₂

  have inj : Function.Injective U₀ := by
    intro x y hxy
    apply hinj
    apply e₀.injective
    rw [hu₀, hu₀, ← hU₀, ← hU₀, hxy]
  have surj : Function.Surjective U₀ := by
    rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    rw [hc, Module.finrank_fintype_fun_eq_card]
  let E₀ : V ≃ₗ[F] (ι → F) := LinearEquiv.ofBijective U₀ ⟨inj, surj⟩
  refine ⟨LinearMap.toMatrix' (U₂ ∘ₗ E₀.symm.toLinearMap), ?_⟩
  set g := LinearMap.toMatrix' (U₂ ∘ₗ E₀.symm.toLinearMap) with hg

  have onForm : ∀ x, e₂ (j x) = g.map (algebraMap F R) *ᵥ e₀ (j x) := by
    intro x
    have h1 : g *ᵥ U₀ x = U₂ x := by
      rw [hg, LinearMap.toMatrix'_mulVec]
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
      congr 1
      exact E₀.symm_apply_apply x
    funext i
    rw [hu₂, hu₀, ← hU₂, ← h1, ← hU₀]
    exact RingHom.map_mulVec (algebraMap F R) g (U₀ x) i

  have onBasis : ∀ i, e₂ (e₀.symm (Pi.single i 1)) = g.map (algebraMap F R) *ᵥ Pi.single i 1 := by
    intro i
    obtain ⟨x, hx⟩ := surj (Pi.single i 1)
    have hs : e₀ (j x) = Pi.single i 1 := by
      rw [hu₀, ← hU₀, hx]
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [hk]
    rw [← hs, LinearEquiv.symm_apply_apply, onForm]
  have hL : (e₂.toLinearMap ∘ₗ e₀.symm.toLinearMap) = Matrix.mulVecLin (g.map (algebraMap F R)) := by
    apply (Pi.basisFun R ι).ext
    intro i
    simp only [Pi.basisFun_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      Matrix.mulVecLin_apply]
    exact onBasis i
  intro w
  have := LinearMap.congr_fun hL (e₀ w)
  simpa using this

theorem std_form {R κ : Type} [CommRing R] [Fintype κ] [DecidableEq κ] (a b : κ ⊕ κ → R) :
    a ⬝ᵥ ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) R) *ᵥ b) =
      (a ∘ Sum.inl) ⬝ᵥ (b ∘ Sum.inr) - (b ∘ Sum.inl) ⬝ᵥ (a ∘ Sum.inr) := by
  rw [Matrix.fromBlocks_mulVec]
  conv_lhs => rw [← Sum.elim_comp_inl_inr a]
  rw [sumElim_dotProduct_sumElim]
  simp only [Matrix.zero_mulVec, Matrix.one_mulVec, zero_add, add_zero, Matrix.neg_mulVec,
    dotProduct_comm (a ∘ Sum.inr)]
  simp only [neg_dotProduct, sub_eq_add_neg]

theorem exists_rat_symplectic_gen {F E R : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [CommRing R]
    [Nontrivial R] [Algebra F R] {α β κ : Type} [Fintype α] [Fintype β] [Fintype κ] [DecidableEq κ]
    {Bf : Matrix α β (R ⊗[F] E) → Matrix α β (R ⊗[F] E) → R} (d₀ d₂ : Darboux Bf κ)
    (inc : Matrix α β E → Matrix α β (R ⊗[F] E)) (hinc : ∀ x a b, inc x a b = (1 : R) ⊗ₜ[F] x a b)
    (hc : Fintype.card κ * 2 = Fintype.card α * Fintype.card β * Module.finrank F E)
    (h₀ : ∀ x : Matrix α β E, ∃ u v : κ → F,
      d₀.e (inc x) = (fun i => algebraMap F R (u i), fun i => algebraMap F R (v i)))
    (h₂ : ∀ x : Matrix α β E, ∃ u v : κ → F,
      d₂.e (inc x) = (fun i => algebraMap F R (u i), fun i => algebraMap F R (v i))) :
    ∃ g : Matrix (κ ⊕ κ) (κ ⊕ κ) F, gᵀ * Matrix.fromBlocks 0 1 (-1) 0 * g = Matrix.fromBlocks 0 1 (-1) 0 ∧
      ∀ w, d₂.e w = GlobalTheory.AdelicSvN.act g (d₀.e w) := by
  classical
  have hφ : Function.Injective (algebraMap F R) := (algebraMap F R).injective

  let j : Matrix α β E →+ Matrix α β (R ⊗[F] E) :=
    { toFun := inc
      map_zero' := by
        ext a b
        simp [hinc]
      map_add' := by
        intro x y
        ext a b
        simp [hinc, TensorProduct.tmul_add] }
  have hj : ∀ (c : F) x, j (c • x) = algebraMap F R c • j x := by
    intro c x
    ext a b
    simp only [j, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hinc, Matrix.smul_apply]
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    simp [Algebra.smul_def]
  have hinj : Function.Injective j := by
    intro x y hxy
    ext a b
    have h := congrFun (congrFun hxy a) b
    simp only [j, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hinc] at h
    apply Algebra.TensorProduct.includeRight_injective (A := R) (B := E) hφ
    simpa [Algebra.TensorProduct.includeRight_apply] using h

  let σ := (LinearEquiv.sumArrowLequivProdArrow κ κ R R).symm
  have hσ : ∀ p : (κ → R) × (κ → R), σ p = Sum.elim p.1 p.2 := fun p => rfl
  have hcard : Module.finrank F (Matrix α β E) = Fintype.card (κ ⊕ κ) := by
    rw [Module.finrank_matrix, Fintype.card_sum, ← hc]
    ring
  have rat : ∀ (d : Darboux Bf κ), (∀ x : Matrix α β E, ∃ u v : κ → F,
      d.e (inc x) = (fun i => algebraMap F R (u i), fun i => algebraMap F R (v i))) →
      ∀ x, ∃ u : κ ⊕ κ → F, (d.e.trans σ) (j x) = fun i => algebraMap F R (u i) := by
    intro d hd x
    obtain ⟨u, v, huv⟩ := hd x
    refine ⟨Sum.elim u v, ?_⟩
    simp only [LinearEquiv.trans_apply, j, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hσ, huv]
    funext i
    cases i <;> rfl
  obtain ⟨g, hg⟩ := GlobalTheory.RatDarboux.exists_rat_matrix j hj hinj hcard (d₀.e.trans σ) (d₂.e.trans σ)
    (rat d₀ h₀) (rat d₂ h₂)
  simp only [LinearEquiv.trans_apply, hσ] at hg
  set G := g.map (algebraMap F R) with hG
  set JR : Matrix (κ ⊕ κ) (κ ⊕ κ) R := Matrix.fromBlocks 0 1 (-1) 0 with hJR

  have form : ∀ (d : Darboux Bf κ) w w',
      Bf w w' = Sum.elim (d.e w).1 (d.e w).2 ⬝ᵥ (JR *ᵥ Sum.elim (d.e w').1 (d.e w').2) := by
    intro d w w'
    rw [hJR, GlobalTheory.RatDarboux.std_form, d.form]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
  have pres : ∀ y y' : κ ⊕ κ → R, y ⬝ᵥ (JR *ᵥ y') = y ⬝ᵥ ((Gᵀ * JR * G) *ᵥ y') := by
    intro y y'
    obtain ⟨w, hw⟩ := (d₀.e.trans σ).surjective y
    obtain ⟨w', hw'⟩ := (d₀.e.trans σ).surjective y'
    simp only [LinearEquiv.trans_apply, hσ] at hw hw'
    have h := (form d₀ w w').symm.trans (form d₂ w w')
    rw [hg, hg, hw, hw'] at h
    rw [h, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose G y, Matrix.vecMul_vecMul,
      ← Matrix.dotProduct_mulVec, Matrix.mul_assoc]
  refine ⟨g, ?_, ?_⟩
  ·
    have hJmap : (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) F).map (algebraMap F R) = JR := by
      ext i k
      rcases i with i | i <;> rcases k with k | k <;>
        simp [hJR, Matrix.one_apply, apply_ite (algebraMap F R)]
    have key : (gᵀ * Matrix.fromBlocks 0 1 (-1) 0 * g).map (algebraMap F R) =
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) F).map (algebraMap F R) := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hJmap, ← hG]
      ext i k
      have h := pres (Pi.single i 1) (Pi.single k 1)
      simp only [single_dotProduct, one_mul, Matrix.mulVec_single_one] at h
      exact h.symm
    exact Matrix.map_injective hφ key
  · intro w
    unfold GlobalTheory.AdelicSvN.act
    rw [← hG, ← hg w]
    exact Prod.ext (Sum.elim_comp_inl (d₂.e w).1 (d₂.e w).2).symm (Sum.elim_comp_inr (d₂.e w).1 (d₂.e w).2).symm

theorem exists_rat_symplectic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (α β κ : Type) [Fintype α] [Fintype β]
  [Fintype κ] [DecidableEq κ] (Bf : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → AF F) (d₀ d₂ : Darboux Bf κ),
  Fintype.card κ * 2 = Fintype.card α * Fintype.card β * Module.finrank F E →
  (∀ x : Matrix α β E, ∃ u v : κ → F, d₀.e (incM F x) = (fun i => algebraMap F (AF F) (u i), fun i => algebraMap F (AF F) (v i))) →
  (∀ x : Matrix α β E, ∃ u v : κ → F, d₂.e (incM F x) = (fun i => algebraMap F (AF F) (u i), fun i => algebraMap F (AF F) (v i))) →
  ∃ g : Matrix (κ ⊕ κ) (κ ⊕ κ) F, gᵀ * Matrix.fromBlocks 0 1 (-1) 0 * g = Matrix.fromBlocks 0 1 (-1) 0 ∧
    ∀ w, d₂.e w = GlobalTheory.AdelicSvN.act g (d₀.e w) := by
  intro F E _ _ _ _ _ α β κ _ _ _ _ Bf d₀ d₂ hc h₀ h₂

  have : Nontrivial (AF F) := (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  exact exists_rat_symplectic_gen (R := AF F) d₀ d₂ (incM F)
    (fun x a b => rfl) hc h₀ h₂

end GlobalTheory.RatDarboux
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocHomV

open GlobalTheory.InertLocFrame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

theorem one_sub_mul_eq_zero (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hmul : ∀ x y, ι (x * y) = ι x * ι y) (t : L) :
    (1 - ι 1) * ι t = 0 := by
  rw [sub_mul, one_mul, ← hmul, one_mul, sub_self]

theorem idem (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hmul : ∀ x y, ι (x * y) = ι x * ι y) :
    (1 - ι 1) * (1 - ι 1) = 1 - ι 1 := by
  rw [mul_sub, mul_one, one_sub_mul_eq_zero ι hmul, sub_zero]

theorem map_mul_map (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hmul : ∀ x y, ι (x * y) = ι x * ι y) {n : ℕ}
    (X Y : Matrix (Fin n) (Fin n) L) : X.map ι * Y.map ι = (X * Y).map ι := by
  ext i j

  simp [Matrix.mul_apply, map_sum, hmul]

theorem smul_map_eq_zero (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hmul : ∀ x y, ι (x * y) = ι x * ι y) {n : ℕ}
    (X : Matrix (Fin n) (Fin n) L) : (1 - ι 1) • X.map ι = 0 := by
  ext i j
  simp [smul_eq_mul, one_sub_mul_eq_zero ι hmul]

def Am {n : ℕ} (P g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L :=
  (P : Matrix (Fin n) (Fin n) L) * ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ *
    ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)

def Mg (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) {n : ℕ} (P g : GL (Fin n) L) : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + (Am P g).map ι

theorem Am_mul {n : ℕ} (P g g' : GL (Fin n) L) : Am P g * Am P g' = Am P (g * g') := by
  unfold Am
  calc _ = (P : Matrix (Fin n) (Fin n) L) * ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ *
        (((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (P : Matrix (Fin n) (Fin n) L)) *
        ((g'⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [Units.inv_mul, Matrix.mul_one, mul_inv_rev, Units.val_mul, Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]

theorem Am_one {n : ℕ} (P : GL (Fin n) L) : Am P 1 = 1 := by
  simp [Am]

theorem Mg_mul (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hmul : ∀ x y, ι (x * y) = ι x * ι y) {n : ℕ} (P g g' : GL (Fin n) L) :
    Mg ι P g * Mg ι P g' = Mg ι P (g * g') := by
  unfold Mg
  rw [add_mul, mul_add, mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.one_mul, smul_smul,
    idem ι hmul, smul_map_eq_zero ι hmul, Matrix.mul_smul, Matrix.mul_one, smul_map_eq_zero ι hmul,
    map_mul_map ι hmul, Am_mul, add_zero, zero_add]

theorem Mg_one (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) {n : ℕ} (P : GL (Fin n) L) : Mg ι P 1 = 1 := by
  unfold Mg
  rw [Am_one]
  ext i j
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

def Phi (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hmul : ∀ x y, ι (x * y) = ι x * ι y) {n : ℕ} (P : GL (Fin n) L) :
    GL (Fin n) L →* GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) where
  toFun g := ⟨Mg ι P g, Mg ι P g⁻¹, by rw [Mg_mul ι hmul, mul_inv_cancel, Mg_one],
    by rw [Mg_mul ι hmul, inv_mul_cancel, Mg_one]⟩
  map_one' := Units.ext (Mg_one ι P)
  map_mul' g g' := Units.ext (Mg_mul ι hmul P g g').symm

theorem key (σL : L →+* L) (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) {n : ℕ} (P JS g : GL (Fin n) L) (J : Matrix (Fin n) (Fin n) E)
    (hJ : ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = gram σL ι P J)
    (hg : Formalism.UG.cT σL (g : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * g = JS) :
    (Am P g)ᵀ * tJ ι J * (Am P g).map σL = tJ ι J := by
  have hpp : ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (P : Matrix (Fin n) (Fin n) L) = 1 := Units.inv_mul P
  have hpp' : (P : Matrix (Fin n) (Fin n) L) * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := Units.mul_inv P
  have hσp' : (P : Matrix (Fin n) (Fin n) L).map σL * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σL = 1 := by
    rw [← Matrix.map_mul, hpp', Matrix.map_one _ (map_zero σL) (map_one σL)]
  have hKK : (JS : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := Units.mul_inv JS
  have hKK' : ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) = 1 := Units.inv_mul JS
  have hgg : ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (g : Matrix (Fin n) (Fin n) L) = 1 := Units.inv_mul g
  have huu : (((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σL)ᵀ * ((g : Matrix (Fin n) (Fin n) L).map σL)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero σL) (map_one σL),
      Matrix.transpose_one]
  have hT : tJ ι J = ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σL := by
    rw [hJ, gram]
    calc tJ ι J = (((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ * (P : Matrix (Fin n) (Fin n) L)ᵀ) * tJ ι J *
        ((P : Matrix (Fin n) (Fin n) L).map σL * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σL) := by
          rw [← Matrix.transpose_mul, hpp', Matrix.transpose_one, Matrix.one_mul, hσp', Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hKi : ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      (((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σL)ᵀ = ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    have hg' : ((g : Matrix (Fin n) (Fin n) L).map σL)ᵀ * (JS : Matrix (Fin n) (Fin n) L) * g = JS := hg
    calc _ = ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          (((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σL)ᵀ *
          ((JS : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) := by
            rw [hKK, Matrix.mul_one]
      _ = ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          (((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σL)ᵀ *
          (((g : Matrix (Fin n) (Fin n) L).map σL)ᵀ * (JS : Matrix (Fin n) (Fin n) L) * g *
            ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) := by rw [hg']
      _ = ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          ((((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σL)ᵀ * ((g : Matrix (Fin n) (Fin n) L).map σL)ᵀ) *
          (JS : Matrix (Fin n) (Fin n) L) * g * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
            simp only [Matrix.mul_assoc]
      _ = _ := by
            rw [huu, Matrix.mul_one, Matrix.mul_assoc ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L), hKK',
              Matrix.mul_one, hgg, Matrix.one_mul]
  calc (Am P g)ᵀ * tJ ι J * (Am P g).map σL
      = ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ *
        (((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          ((P : Matrix (Fin n) (Fin n) L)ᵀ * tJ ι J * (P : Matrix (Fin n) (Fin n) L).map σL) *
          (((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σL)ᵀ) *
        ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σL := by
          simp only [Am, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.map_mul, Matrix.transpose_map,
            Matrix.mul_assoc]
    _ = tJ ι J := by rw [← gram, ← hJ, hKi, ← hT]

theorem mem (σ : E →ₐ[F] E) (v : Pl (F := F)) (σL : L →+* L) (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))
    (hsupp : ∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) (hmul : ∀ x y, ι (x * y) = ι x * ι y)
    (hσ : ∀ x, ι (σL x) = cA σ (ι x)) {n : ℕ} (P JS g : GL (Fin n) L) (J : Matrix (Fin n) (Fin n) E)
    (hJ : ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = gram σL ι P J)
    (hg : Formalism.UG.cT σL (g : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * g = JS) :
    (Mg ι P g)ᵀ * incM F J * (Mg ι P g).map (cA σ) = incM F J := by
  have hce : cA σ (ι 1) = ι 1 := by rw [← hσ, map_one]
  have hMT : (Mg ι P g)ᵀ = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + (Am P g)ᵀ.map ι := by
    simp [Mg, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_map]
  have hMc : (Mg ι P g).map (cA σ) =
      (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + ((Am P g).map σL).map ι := by
    ext i j
    by_cases h : i = j <;> simp [Mg, h, Matrix.one_apply, ← hσ, hce]
  have hsplit : incM F J = (1 - ι 1) • incM F J + (tJ ι J).map ι := by
    ext i j
    have hex : ∃ x, ι x = ι 1 * inclR (F := F) (AF F) (J i j) := (hsupp _).1 (fun u hu => by
      rw [← smul_mul_assoc, (hsupp (ι 1)).2 ⟨1, rfl⟩ u hu, zero_mul])
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, incM, tJ]
    rw [pre_spec ι hex]
    ring
  have h1 : (Am P g)ᵀ.map ι * incM F J = ((Am P g)ᵀ * tJ ι J).map ι := by
    calc (Am P g)ᵀ.map ι * incM F J = (Am P g)ᵀ.map ι * ((1 - ι 1) • incM F J + (tJ ι J).map ι) := by
          rw [← hsplit]
      _ = ((1 - ι 1) • (Am P g)ᵀ.map ι) * incM F J + (Am P g)ᵀ.map ι * (tJ ι J).map ι := by
          rw [Matrix.mul_add, Matrix.mul_smul, ← Matrix.smul_mul]
      _ = _ := by rw [smul_map_eq_zero ι hmul, Matrix.zero_mul, zero_add, map_mul_map ι hmul]
  have hL : (Mg ι P g)ᵀ * incM F J = (1 - ι 1) • incM F J + ((Am P g)ᵀ * tJ ι J).map ι := by
    rw [hMT, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, h1]
  have e1 : ((1 - ι 1) • incM F J) * ((1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) = (1 - ι 1) • incM F J := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, idem ι hmul]
  have e2 : ((1 - ι 1) • incM F J) * ((Am P g).map σL).map ι = 0 := by
    rw [Matrix.smul_mul, ← Matrix.mul_smul, smul_map_eq_zero ι hmul, Matrix.mul_zero]
  have e3 : ((Am P g)ᵀ * tJ ι J).map ι * ((1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) = 0 := by
    rw [Matrix.mul_smul, Matrix.mul_one, smul_map_eq_zero ι hmul]
  rw [hL, hMc, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, e1, e2, e3, map_mul_map ι hmul,
    key σL ι P JS g J hJ hg, add_zero, zero_add, ← hsplit]

theorem exists_homV : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl (F := F)) (n : ℕ) (X : Spc F E n) (L : Type) [Field L] (σL : L →+* L)
    (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) → (∀ x, ι (σL x) = cA σ (ι x)) →
      ∀ (P JS : GL (Fin n) L), ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = GlobalTheory.InertLocFrame.gram σL ι P X.J →
      ∃ iV : Formalism.UG.UJ σL (JS : Matrix (Fin n) (Fin n) L) →* UA σ X.J, ∀ g,
        mat (iV g) = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) +
          ((P : Matrix (Fin n) (Fin n) L) * (((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ *
            ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).map ι := by
  intro F E _ _ _ _ _ σ v n X L _ σL ι hsupp hmul hσ P JS hJ
  exact ⟨((Phi ι hmul P).comp (Formalism.UG.UJ σL (JS : Matrix (Fin n) (Fin n) L)).subtype).codRestrict
    (UG (cA σ) (incM F X.J)) (fun g => mem σ v σL ι hsupp hmul hσ P JS g.1 X.J hJ g.2), fun g => rfl⟩

end GlobalTheory.InertLocHomV

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.InertLagChar

variable {F : Type} [Field F] [NumberField F] {v : Pl (F := F)} {κ : Type} [Fintype κ]

def diagW (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)) (Φ : (κ ⊕ κ → Fv F v) → ℂ)
    (w : (κ → Fv F v) × (κ → Fv F v)) : ℂ :=
  ∫ x, schr ψ (Sum.elim w.1 0, Sum.elim w.2 0) Φ (Sum.elim x x) ∂μ

def lagInt (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)) {N : ℕ} (ν : @Measure (Fin N → Fv F v) (borel _))
    (j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v)) (Φ : (κ ⊕ κ → Fv F v) → ℂ) : ℂ :=
  ∫ y, diagW ψ μ Φ (j y) ∂ν


open NumberField IsDedekindDomain MeasureTheory in
open scoped TensorProduct Matrix in
variable {F : Type} [Field F] [NumberField F] {v : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} {κ : Type} [Fintype κ] in
theorem _root_.GlobalTheory.InertLagChar.diagW_zero (ψ : AddChar (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ℂ)
    (μ : @Measure (κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (borel _)) (Φ : (κ ⊕ κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) :
    _root_.GlobalTheory.InertLagChar.diagW ψ μ Φ 0 = ∫ x, Φ (Sum.elim x x) ∂μ := by
  unfold _root_.GlobalTheory.InertLagChar.diagW _root_.GlobalTheory.WeilM.schr
  simp

end GlobalTheory.InertLagChar
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.MBLow.Cl GlobalTheory.MBLow.Cl.CubHol
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.Cl.CubHol

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

def phiXY (ν : NumOf D ℂ N) (d : AB N.toNumB g) (x y : Fin g → ℂ) : (DegPre.BF D ℂ).left ⟶ (G3 D.P.A).left :=
  (lift (fst _ _ ≫ ν.eA (d.ex x)) (lift (fst _ _ ≫ ν.eA (d.ex y)) (snd _ _))).left

theorem ptB_phiXY (ν : NumOf D ℂ N) (d : AB N.toNumB g) (x y z : Fin g → ℂ) :
    ptB ν d z ≫ phiXY ν d x y = pt3 ν d x y z := by
  rw [ptB, phiXY, pt3, ← Over.comp_left, comp_lift, lift_fst_assoc, comp_lift, lift_fst_assoc, lift_snd,
    Category.id_comp, Category.id_comp]

theorem isOpen_and_differentiableOn_valF_pt3_cubW : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ} (ν : NumOf D ℂ N) (d : AB N.toNumB g), Geo ν d → ∀ (x y : Fin g → ℂ) (j : thK → D.P.L.ι), IsOpen {z | ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j} ∧ DifferentiableOn ℂ (fun z => valF (pt3 ν d x y z) (cubW D j) (D.cub.t.s j).val) {z | ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j} := by
  intro R _ _ D _ N g ν d G x y j
  have hs : {z | ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j} = {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ (phiXY ν d x y ⁻¹ᵁ cubW D j)} := by
    ext z
    simp only [Set.mem_setOf_eq, ← ptB_phiXY ν d x y z, Scheme.Hom.comp_preimage]
  obtain ⟨ho, hd⟩ := G.hol (phiXY ν d x y ⁻¹ᵁ cubW D j)
    (((phiXY ν d x y).appLE (cubW D j) (phiXY ν d x y ⁻¹ᵁ cubW D j) le_rfl).hom (D.cub.t.s j).val)
  rw [hs]
  refine ⟨ho, hd.congr fun z hz => ?_⟩
  have e := UnitVal.valF_appLE' (x := ptB ν d z) (phiXY ν d x y) (cubW D j) le_rfl hz (D.cub.t.s j).val
  rw [ptB_phiXY] at e
  exact e.symm

end GlobalTheory.MBLow.Cl.CubHol

end
end
