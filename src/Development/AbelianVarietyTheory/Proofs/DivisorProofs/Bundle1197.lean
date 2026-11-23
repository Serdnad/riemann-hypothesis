module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankRiemannRochNsmulHyperplane
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory.FormSection

theorem exists_section : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), L.FG →
    ∀ x : Fin n → E, (∃ z ∈ L, form σ J z x ≠ 0) →
    ∃ y₀ : Fin n → E, form σ J y₀ x = 1 ∧ ∀ z ∈ L, form σ J z x • y₀ ∈ L := by
  intro F E _ _ _ _ _ σ n J L hL x ⟨z₀, hz₀L, hz₀⟩
  classical

  let φ : (Fin n → E) →ₗ[𝓞 E] E :=
    { toFun := fun z => form σ J z x
      map_add' := fun a b => by simp [form, add_dotProduct]
      map_smul' := fun a z => by
        simp only [form, RingHom.id_apply]
        rw [← algebraMap_smul E a z, smul_dotProduct, smul_eq_mul, Algebra.smul_def] }
  have hφ : ∀ z, φ z = form σ J z x := fun _ => rfl
  have hφE : ∀ (c : E) z, form σ J (c • z) x = c * form σ J z x := by
    intro c z; simp [form, smul_dotProduct]
  let I : Submodule (𝓞 E) E := L.map φ
  have hIfg : I.FG := hL.map φ
  let I' : FractionalIdeal (nonZeroDivisors (𝓞 E)) E := ⟨I, FractionalIdeal.isFractional_of_fg hIfg⟩
  have hmemI : ∀ z ∈ L, form σ J z x ∈ I' := fun z hz => ⟨z, hz, rfl⟩
  have hI0 : I' ≠ 0 := by
    intro h
    have := hmemI z₀ hz₀L
    rw [h, FractionalIdeal.mem_zero_iff] at this
    exact hz₀ this
  have hone : I' * I'⁻¹ = 1 := mul_inv_cancel₀ hI0
  let S : Submodule (𝓞 E) E :=
    { carrier := {e | ∃ y₀ : Fin n → E, form σ J y₀ x = e ∧ ∀ c ∈ I, c • y₀ ∈ L}
      add_mem' := by
        rintro _ _ ⟨y₁, rfl, h₁⟩ ⟨y₂, rfl, h₂⟩
        refine ⟨y₁ + y₂, by simp [form, add_dotProduct], fun c hc => ?_⟩
        rw [smul_add]; exact L.add_mem (h₁ c hc) (h₂ c hc)
      zero_mem' := ⟨0, by simp [form], fun c _ => by simp⟩
      smul_mem' := by
        rintro a _ ⟨y, rfl, h⟩
        refine ⟨a • y, ?_, fun c hc => ?_⟩
        · rw [← hφ, ← hφ, map_smul]
        · rw [smul_comm]; exact L.smul_mem a (h c hc) }
  have hle : I * ((I'⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) ≤ S := by
    refine Submodule.mul_le.mpr fun i hi j hj => ?_
    obtain ⟨z, hz, rfl⟩ := hi
    refine ⟨j • z, ?_, fun c hc => ?_⟩
    · rw [hφE, hφ, mul_comm]
    · have hcj : j * c ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :=
        (FractionalIdeal.mem_inv_iff hI0).mp hj c hc
      obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).mp hcj
      rw [smul_smul, mul_comm, ← ha, algebraMap_smul]
      exact L.smul_mem a hz
  have h1 : (1 : E) ∈ S := by
    apply hle
    have : (1 : E) ∈ ((I' * I'⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) := by
      rw [hone]; exact (FractionalIdeal.mem_one_iff _).mpr ⟨1, map_one _⟩
    rwa [FractionalIdeal.coe_mul] at this
  obtain ⟨y₀, hy₀, hL'⟩ := h1
  exact ⟨y₀, hy₀, fun z hz => hL' _ (hmemI z hz)⟩

end GlobalTheory.FormSection
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertVacLag

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def lagAt {n d m : ℕ} (v : Pl (F := F)) (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :=
  {u | At (evFin F v) u ∧ ∃ z : Matrix (Fin n) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), u = z * Cᵀ}

def IsLagrAt (σ : E →ₐ[F] E) {d m : ℕ} (W : Spc F E d) (v : Pl (F := F)) (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Prop :=
  IsLagr (Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ) (JR (Fv F v) W.J) (C.map (compFin F E v))

def HeisInv {σ : E →ₐ[F] E} {n d m : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (v : Pl (F := F)) (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (l : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ u ∈ lagAt v C, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
    Acts (evFin F v) (M.co.rho ψ u) φ φ₁ → l φ₁ = l φ

end GlobalTheory.InertVacLag
end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Div.CoordOpp

theorem piW_inclR {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) (e : E) :
    piW t (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F) e) = t e := by
  have h1 : compFin F E v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F) e) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Fv F v) e := by
    simp [compFin, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]
  simp only [piW, RingHom.comp_apply, h1]
  exact splitProj_inclR t e

theorem piW_cA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    piW t (cA σ z) = piW (t.comp σ) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [piW, cA, compFin, splitProj]
  | add x y hx hy => simp [map_add (f := _), hx, hy]

theorem incM_map_piW {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) {m k : Type} (J : Matrix m k E) :
    (incM F J).map (piW t) = J.map t := by
  ext i j
  simp [incM, piW_inclR]

theorem unit_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) :
    ((mat g).map (piW t))ᵀ * J.map t * (mat g).map (piW (t.comp σ)) = J.map t := by
  have hg := g.2
  change ((mat g))ᵀ * incM F J * (mat g).map (cA σ) = incM F J at hg
  have := congrArg (fun M => M.map (piW t)) hg
  simp only [Matrix.map_mul, Matrix.transpose_map, incM_map_piW] at this
  have e2 : ((mat g).map (cA σ)).map (piW t) = (mat g).map (piW (t.comp σ)) := by
    ext i j; simp [piW_cA]
  rw [e2] at this
  simpa [Matrix.transpose_map] using this

end GlobalTheory.Div.CoordOpp

open GlobalTheory.Div.CoordOpp in
theorem GlobalTheory.Div.CoordOpp.coord_opp_conj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (g : UA σ X.J) (h : UA σ W.J)
    (x : Matrix (Fin n) (Fin d) (AE F E)),
    ((mat g).map (piW t))ᵀ * -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (mat g * x * (mat h)ᵀ).map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1) * (mat h).map (piW t) = -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (x).map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1) := by
  intro F E _ _ _ _ _ σ n d X W v t g h x
  have hg := unit_map σ g t
  have hh := unit_map σ h t
  simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.map_mul,
    Matrix.transpose_map, Matrix.mul_neg, Matrix.neg_mul, neg_inj]
  set gt := (mat g).map (piW t)
  set gb := (mat g).map (piW (t.comp σ))
  set ht := (mat h).map (piW t)
  set hb := (mat h).map (piW (t.comp σ))
  set xb := x.map (piW (t.comp σ))
  have hh' : hbᵀ * (W.J.map t)ᵀ * ht = (W.J.map t)ᵀ := by
    have := congrArg Matrix.transpose hh
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  calc gtᵀ * (X.J.map t * (gb * xb * ((mat h)ᵀ).map (piW (t.comp σ))) * (W.J.map t)ᵀ) * ht
      = (gtᵀ * X.J.map t * gb) * xb * (hbᵀ * (W.J.map t)ᵀ * ht) := by
        simp only [hb, Matrix.transpose_map, Matrix.mul_assoc]
    _ = X.J.map t * xb * (W.J.map t)ᵀ := by rw [hg, hh']
end

section

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.RealActs

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def DerOn (N : Submodule ℂ (SInf F κ)) (T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) : Prop :=
  ∃ D : SInf F κ →ₗ[ℂ] SInf F κ, (∀ f ∈ N, D f ∈ N) ∧ ∀ f ∈ N, ∀ f₁ : SInf F κ, ActsD (evI F) T f f₁ ↔ f₁ = D f

def OpOn (N : Submodule ℂ (SInf F κ)) (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) : Prop :=
  ∃ D : SInf F κ →ₗ[ℂ] SInf F κ, (∀ f ∈ N, D f ∈ N) ∧ ∀ f ∈ N, ∀ f₁ : SInf F κ, Acts (evI F) T f f₁ ↔ f₁ = D f

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def PolActs (B : Base F E) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) : Prop :=
  (∀ γ ∈ Lines σ X, DerOn (M.Pol B.ψ B.emb) (fun t => om (γ (Multiplicative.ofAdd t), 1))) ∧
  (∀ k ∈ KInf σ X B.emb, OpOn (M.Pol B.ψ B.emb) (om (k, 1))) ∧
  (∀ γ ∈ Lines σ W, DerOn (M.Pol B.ψ B.emb) (fun t => om (1, γ (Multiplicative.ofAdd t)))) ∧
  ∀ k ∈ KInf σ W B.emb, OpOn (M.Pol B.ψ B.emb) (om (1, k))

def KerStab (B : Base F E) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) {P : Type}
    [AddCommGroup P] [Module ℂ P] (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) : Prop :=
  (∀ γ ∈ Lines σ W, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
    ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → p f = 0 → p f₁ = 0) ∧
  ∀ k ∈ KInf σ W B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
    Acts (evI F) (om (1, k)) f f₁ → p f = 0 → p f₁ = 0

def Irred (B : Base F E) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) {P : Type}
    [AddCommGroup P] [Module ℂ P] (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) : Prop :=
  ∀ N : Submodule ℂ P,
    (∀ γ ∈ Lines σ W, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → p f ∈ N → p f₁ ∈ N) →
    (∀ k ∈ KInf σ W B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, k)) f f₁ → p f ∈ N → p f₁ ∈ N) → N = ⊥ ∨ N = ⊤

end GlobalTheory.RealActs

end
end

section

noncomputable section

namespace GlobalTheory.ThK.PolynomialMatching

open scoped TensorProduct Classical
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

def PolMatchOn (B : Base F E) (G : Geo σ a a') (X : Chars F E) (R : RealMaps F a a') (Rf : FinMaps F a a')
    (T : Finset (Pl F)) (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) (Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ) : Prop :=
  ∃ (m m' : ℕ) (f : Fin m → SInf F _) (φ : Fin m → ∀ v : Pl F, (_ → Fv F v) → ℂ)
    (f' : Fin m' → SInf F _) (φ' : Fin m' → ∀ v : Pl F, (_ → Fv F v) → ℂ),
    (∀ i, f i ∈ G.M.Pol B.ψ B.emb ∧ (∀ v, φ i v ∈ SB _) ∧ ∀ v ∉ T, φ i v = G.M.vac v) ∧
    (∀ j, f' j ∈ G.M'.Pol B.ψ B.emb ∧ (∀ v, φ' j v ∈ SB _) ∧ ∀ v ∉ T, φ' j v = G.M'.vac v) ∧
    Φ = ∑ i, pure (f i) (φ i) ∧ Φ' = ∑ j, pure (f' j) (φ' j) ∧
    ∑ i, R.p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p v (φ i v)) =
      ∑ j, R.p' (f' j) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φ' j v))

theorem polMatch_iff (B : Base F E) (G : Geo σ a a') (X : Chars F E) (R : RealMaps F a a') (Rf : FinMaps F a a')
    (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) (Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ) :
    PolMatch B G X R Rf Φ Φ' ↔ ∃ T : Finset (Pl F), X.T ⊆ T ∧ PolMatchOn B G X R Rf T Φ Φ' := Iff.rfl

end GlobalTheory.ThK.PolynomialMatching
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix

namespace GlobalTheory.AdelicSvN

variable {F : Type} [Field F]

def act {R : Type} [CommRing R] [Algebra F R] {κ : Type} [Fintype κ] (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F)
    (w : (κ → R) × (κ → R)) : (κ → R) × (κ → R) :=
  ((g.map (algebraMap F R) *ᵥ Sum.elim w.1 w.2) ∘ Sum.inl, (g.map (algebraMap F R) *ᵥ Sum.elim w.1 w.2) ∘ Sum.inr)

theorem act_one {R : Type} [CommRing R] [Algebra F R] {κ : Type} [Fintype κ] [DecidableEq κ]
    (w : (κ → R) × (κ → R)) : act (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) w = w := by
  have h : (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F).map (algebraMap F R) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  simp only [act, h, Matrix.one_mulVec]
  rfl

theorem act_mul {R : Type} [CommRing R] [Algebra F R] {κ : Type} [Fintype κ]
    (g h : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (w : (κ → R) × (κ → R)) : act (g * h) w = act g (act h w) := by
  have e : (g * h).map (algebraMap F R) = g.map (algebraMap F R) * h.map (algebraMap F R) :=
    Matrix.map_mul (f := algebraMap F R)
  simp only [act, e, ← Matrix.mulVec_mulVec, Sum.elim_comp_inl_inr]


variable (F) in
def gens (κ : Type) [Fintype κ] [DecidableEq κ] : Set (Matrix (κ ⊕ κ) (κ ⊕ κ) F) :=
  {g | ∃ A : Matrix κ κ F, IsUnit A.det ∧ g = Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ} ∪
    {g | ∃ C : Matrix κ κ F, Cᵀ = C ∧ g = Matrix.fromBlocks 1 0 (-C) 1} ∪ {Matrix.fromBlocks 0 1 (-1) 0}

variable [NumberField F]

def Realised (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ] (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F) : Prop :=
  ∃ S : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ,
    (∀ φ ∈ schA F κ, S φ ∈ schA F κ) ∧ (∀ φ ∈ schA F κ, ∃ φ' ∈ schA F κ, S φ' = φ) ∧
    (∀ l ∈ (adeleClass F).adm κ, ∃ l' ∈ (adeleClass F).adm κ, ∀ φ ∈ schA F κ, l' φ = l (S φ)) ∧
    ∀ w, ∀ φ ∈ schA F κ, S (schr ψ w φ) = schr ψ (act g w) (S φ)

theorem realised_one (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ] [DecidableEq κ] :
    Realised ψ (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) :=
  ⟨id, fun φ h => h, fun φ h => ⟨φ, h, rfl⟩, fun l hl => ⟨l, hl, fun _ _ => rfl⟩,
    fun w φ _ => by rw [act_one]; rfl⟩

theorem Realised.mul {ψ : AddChar (AF F) ℂ} {κ : Type} [Fintype κ] {g h : Matrix (κ ⊕ κ) (κ ⊕ κ) F}
    (hg : Realised ψ g) (hh : Realised ψ h) : Realised ψ (g * h) := by
  obtain ⟨S, hS, hSs, hSa, hSi⟩ := hg
  obtain ⟨T, hT, hTs, hTa, hTi⟩ := hh
  refine ⟨S ∘ T, fun φ hφ => hS _ (hT φ hφ), fun φ hφ => ?_, fun l hl => ?_, fun w φ hφ => ?_⟩
  · obtain ⟨φ₁, h₁, rfl⟩ := hSs φ hφ
    obtain ⟨φ₂, h₂, rfl⟩ := hTs φ₁ h₁
    exact ⟨φ₂, h₂, rfl⟩
  · obtain ⟨l₁, hl₁, e₁⟩ := hSa l hl
    obtain ⟨l₂, hl₂, e₂⟩ := hTa l₁ hl₁
    exact ⟨l₂, hl₂, fun φ hφ => (e₂ φ hφ).trans (e₁ _ (hT φ hφ))⟩
  · simp only [Function.comp_apply]
    rw [hTi w φ hφ, hSi _ _ (hT φ hφ), act_mul]

end GlobalTheory.AdelicSvN
end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SympInv
open Matrix
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem hTens_eq_trace (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    GlobalTheory.WeilM.hTens c JA JB x y = trace (xᵀ * JA * y.map c * JBᵀ) := by
  simp only [GlobalTheory.WeilM.hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : ∀ i : α, ∑ k : α, ∑ l : β, x i j * JA i k * JB j l * c (y k l) =
      ∑ l : β, ∑ k : α, x i j * JA i k * c (y k l) * JB j l := fun i => by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact Finset.sum_comm

theorem hTens_act (JA : Matrix α α E) (JB : Matrix β β E) (G : Matrix α α E) (H : Matrix β β E)
    (hG : Gᵀ * JA * G.map c = JA) (hH : Hᵀ * JB * H.map c = JB) (x y : Matrix α β E) :
    GlobalTheory.WeilM.hTens c JA JB (G * x * Hᵀ) (G * y * Hᵀ) = GlobalTheory.WeilM.hTens c JA JB x y := by
  rw [hTens_eq_trace, hTens_eq_trace]
  have e1 : (G * y * Hᵀ).map c = G.map c * y.map c * (H.map c)ᵀ := by
    ext i j

    simp [Matrix.mul_apply, map_sum, map_mul]
  have e2 : (H.map c)ᵀ * JBᵀ * H = JBᵀ := by
    conv_rhs => rw [← hH]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [e1, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [show H * (xᵀ * Gᵀ) * JA * (G.map c * y.map c * (H.map c)ᵀ) * JBᵀ =
      H * (xᵀ * (Gᵀ * JA * G.map c) * y.map c * ((H.map c)ᵀ * JBᵀ)) by simp only [Matrix.mul_assoc]]
  rw [Matrix.trace_mul_comm, hG, Matrix.mul_assoc _ _ H, e2]

end GlobalTheory.SympInv

namespace GlobalTheory.SympInv

theorem symp_act : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (g : UA σ X.J) (h : UA σ W.J) (x u : Matrix (Fin n) (Fin d) (AE F E)),
    symp (cA σ) (-1) (incM F X.J) (incM F W.J) (mat g * x * (mat h)ᵀ) (mat g * u * (mat h)ᵀ) =
      symp (cA σ) (-1) (incM F X.J) (incM F W.J) x u := by
  intro F E _ _ _ _ _ σ n d X W g h x u
  have hg : (mat g)ᵀ * incM F X.J * (mat g).map (cA σ) = incM F X.J := g.2
  have hh : (mat h)ᵀ * incM F W.J * (mat h).map (cA σ) = incM F W.J := h.2
  unfold GlobalTheory.WeilM.symp
  rw [hTens_act (cA σ) (incM F X.J) (incM F W.J) (mat g) (mat h) hg hh x u]

end GlobalTheory.SympInv
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocFrame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]


open Classical in
def pre (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : L := if h : ∃ x, ι x = z then h.choose else 0

theorem pre_spec (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (h : ∃ x, ι x = z) : ι (pre ι z) = z := by
  unfold pre
  rw [dite_eq_left h]
  exact h.choose_spec

def tJ (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) {m n : Type} (J : Matrix m n E) : Matrix m n L :=
  fun i j => pre ι (ι 1 * inclR (F := F) (AF F) (J i j))

def gram (σL : L →+* L) (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) {n : ℕ} (P : GL (Fin n) L) (J : Matrix (Fin n) (Fin n) E) :
    Matrix (Fin n) (Fin n) L :=
  (P : Matrix (Fin n) (Fin n) L)ᵀ * tJ ι J * (P : Matrix (Fin n) (Fin n) L).map σL

def xm (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) {n d : ℕ} (PV : GL (Fin n) L) (PW : GL (Fin d) L) :
    Matrix (Fin d) (Fin n) L →+ Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) where
  toFun x := ((PV : Matrix (Fin n) (Fin n) L) * xᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ).map ι
  map_zero' := by ext i j; simp
  map_add' x y := by ext i j; simp [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

theorem xm_apply (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) {n d : ℕ} (PV : GL (Fin n) L) (PW : GL (Fin d) L) (x : Matrix (Fin d) (Fin n) L) :
    xm ι PV PW x = ((PV : Matrix (Fin n) (Fin n) L) * xᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ).map ι := rfl

end GlobalTheory.InertLocFrame

end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory

theorem matrix_mem_span_incM : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (m n : ℕ)
    (u : Matrix (Fin m) (Fin n) (AF F ⊗[F] E)),
    u ∈ Submodule.span (AF F) (Set.range (incM F : Matrix (Fin m) (Fin n) E → Matrix (Fin m) (Fin n) (AF F ⊗[F] E))) := by
  intro F E _ _ _ _ _ m n u
  classical
  rw [Matrix.matrix_eq_sum_single u]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  generalize u i j = a
  induction a using TensorProduct.induction_on with
  | zero => rw [Matrix.single_zero]; exact Submodule.zero_mem _
  | add x y hx hy => rw [Matrix.single_add]; exact Submodule.add_mem _ hx hy
  | tmul a e =>
    have h : Matrix.single i j (a ⊗ₜ[F] e) = a • incM F (Matrix.single i j e) := by
      ext k l
      simp only [incM, Matrix.smul_apply, Matrix.map_apply, Matrix.single, Matrix.of_apply]
      split_ifs
      · change _ = a • ((1 : AF F) ⊗ₜ[F] e)
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      · simp
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

theorem _root_.GlobalTheory.T.intersection_divisor_eq_selfIntersection_presented : ∀ (Y : Var ℂ) (Δ : Y.Dv) (L : LB Y.X) (r : L.ι → Y.Fnˣ), L.IsLB → Presents Δ L r → Y.inter (fun _ => Δ) = topSelfIntersection ℂ L Y.dim := by
  first | exact @GlobalTheory.ChernDegree.inter_const_eq_topSelf_of_presents | exact GlobalTheory.ChernDegree.inter_const_eq_topSelf_of_presents | (intros; apply GlobalTheory.ChernDegree.inter_const_eq_topSelf_of_presents <;> assumption)
end
