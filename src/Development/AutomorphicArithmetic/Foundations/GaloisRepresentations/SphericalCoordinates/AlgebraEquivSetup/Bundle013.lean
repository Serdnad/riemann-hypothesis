module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.TypeSlice
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.MapWopWmap

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open GlobalTheory.LFun (KGL)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.W2.Seed

def memFn {X : Type} [Group X] (K KM K₀ : Subgroup X) (h y : X) : ℂ :=
  (Nat.card {k : K ⧸ KM.subgroupOf K // h * (k.out : X) * y ∈ K₀} : ℕ)

def MemSum : Prop := ∀ (X : Type) [Group X] (K KM K₀ : Subgroup X) (h : X), K₀ ≤ K → KM.relIndex K ≠ 0 →
  (∀ k ∈ K, ∀ u ∈ KM, k * u * k⁻¹ ∈ KM) → (∀ k ∈ K, ∀ u ∈ KM, h * k * u * (h * k)⁻¹ ∈ K₀) →
  memFn K KM K₀ h ∈ Hecke ℂ K₀ ∧ (∀ y, memFn K KM K₀ h y ≠ 0 → ∃ k ∈ K, h * k * y ∈ K₀) ∧
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Φ : X → V), (∀ k ∈ K₀, ∀ g, Φ (g * k) = Φ g) → ∀ g,
    hAct K₀ (memFn K KM K₀ h) Φ g = ∑ᶠ k : K ⧸ KM.subgroupOf K, Φ (g * (h * (k.out : X))⁻¹)

def SumDoset : Prop := ∀ (X : Type) [Group X] (K KM : Subgroup X) (h : X), KM ≤ K → KM.relIndex K ≠ 0 →
  (∀ u ∈ KM, h * u * h⁻¹ ∈ K) →
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Φ : X → V), (∀ k ∈ K, ∀ g, Φ (g * k) = Φ g) →
    (∀ k ∈ K, ∀ u ∈ KM, k * u * k⁻¹ ∈ KM) → ∀ g,
    ∑ᶠ k : K ⧸ KM.subgroupOf K, Φ (g * (h * (k.out : X))⁻¹) =
      ((KM.relIndex (K ⊓ K.comap (MulAut.conj h).toMonoidHom) : ℕ) : ℂ) • hAct K (dosetInd ℂ K h⁻¹) Φ g

def TyLev.Acts {X M : Type} [Group X] [Group M] (T : TyLev X M) (ψ : X → ℂ) (c : ℂ) (h : X) : Prop :=
  ψ ∈ Hecke ℂ T.K₀ ∧ T.L.pr h = 1 ∧
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Φ : X → V), T.IsTy Φ → hAct T.K₀ ψ Φ = c • hAct T.K₀ (T.tf h) Φ

def TyLev.Triv {X M : Type} [Group X] [Group M] (T : TyLev X M) (K : Subgroup X) : Prop :=
  K ≤ T.K ∧ ∀ k ∈ K, ∀ h, T.ψ ⟨T.L.pr k, h⟩ = 1

def MemAct : Prop := ∀ (X M M' : Type) [Group X] [Group M] [Group M'] (T : TyLev X M) (L' : Loc X M') (Kw : Subgroup M'),
  L'.Fact T.K Kw → T.L.Apart L' → ∀ K KM : Subgroup X, T.Triv K → L'.Fact K Kw → T.K₀ ≤ K → KM ≤ T.K₀ → KM.relIndex K ≠ 0 →
  (∀ k ∈ K, ∀ u ∈ KM, k * u * k⁻¹ ∈ KM) → ∀ (t : M') (z h : X), T.Cen z → h⁻¹ = L'.loc t * z →
  (∀ k ∈ K, ∀ u ∈ KM, h * k * u * (h * k)⁻¹ ∈ T.K₀) →
  T.Acts (memFn K KM T.K₀ h) (KM.relIndex (K ⊓ K.comap (MulAut.conj h).toMonoidHom) : ℕ) (L'.loc t * z)

def MemDeck : Prop := ∀ (X M : Type) [Group X] [Group M] (T : TyLev X M) (K : Subgroup X), T.Triv K → ∀ k ∈ K,
  (∀ u ∈ T.K₀, k * u * k⁻¹ ∈ T.K₀) → T.Acts (memFn T.K₀ T.K₀ T.K₀ k) 1 1

def RelOf : Prop := ∀ (X M J : Type) [Group X] [Group M] (T : TyLev X M) (ψ : J → X → ℂ) (c : J → ℂ) (h : J → X) (hu : X) (u' : X → ℂ),
  (∀ j, T.Acts (ψ j) (c j) (h j)) → T.L.pr hu = 1 → u' ∈ Hecke ℂ T.K₀ →
  (∀ i j, conv T.K₀ (T.tf (h i)) (T.tf (h j)) = conv T.K₀ (T.tf (h j)) (T.tf (h i))) →
  (∀ j, conv T.K₀ (T.tf hu) (T.tf (h j)) = conv T.K₀ (T.tf (h j)) (T.tf hu)) → conv T.K₀ u' (T.tf hu) = T.tf 1 →
  Spc.Rel (conv T.K₀) ψ (T.tf 1) (T.tf hu) u'

def SphComm : Prop := ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : Plc E) (t t' : GL (Fin n) (w.adicCompletion E)),
  conv (KGL w (n := n)) (dosetInd ℂ (KGL w (n := n)) t) (dosetInd ℂ (KGL w (n := n)) t') = conv (KGL w (n := n)) (dosetInd ℂ (KGL w (n := n)) t') (dosetInd ℂ (KGL w (n := n)) t)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p}

def Tr.lv (T : Tr S) (K : Subgroup (GUf E n)) : Subgroup S.G.GAf := K.comap T.sec

def AtApart : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S) (hc : LocComm) (w : Plc E) (hw : IsSplitAt w) (hp : (p : 𝓞 E) ∉ w.asIdeal),
  (∀ x, T.sec ((T.at hc w hw hp).loc x) = CertificateRingHomMap.loc hw x) ∧
  ∀ (w' : Plc E) (hw' : IsSplitAt w') (hp' : (p : 𝓞 E) ∉ w'.asIdeal), GlobalTheory.Cong.Apart w w' → (T.at hc w hw hp).Apart (T.at hc w' hw' hp')

def LevFact : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S) (hc : LocComm) (S₀ : Finset (Plc E)) (Kw : ∀ w : Plc E, Subgroup (GL (Fin n) (w.adicCompletion E)))
  (w : Plc E) (hw : IsSplitAt w) (hp : (p : 𝓞 E) ∉ w.asIdeal), CertificateRingHomMap.cj w ∉ S₀ →
  (w ∈ S₀ → (T.at hc w hw hp).Fact (T.lv (lev S₀ Kw)) (Kw w)) ∧ (w ∉ S₀ → (T.at hc w hw hp).Fact (T.lv (lev S₀ Kw)) (KGL w (n := n)))

def IntConj : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (g : GUf E n) (w : Plc E), 0 < n →
  (sim g ∈ ZU → comp w g ∈ KGL w (n := n) → comp (CertificateRingHomMap.cj w) g ∈ KGL (CertificateRingHomMap.cj w) (n := n)) ∧
  ((∀ u, comp u g ∈ KGL u (n := n)) → sim g ∈ ZU) ∧ {u : Plc E | comp u g ∉ KGL u (n := n)}.Finite

def KNOpen : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S) (N : ℕ), 0 < N → IsOpen (((S.L.KN N).comap T.j : Subgroup (GUf E n)) : Set (GUf E n))

def KNIdx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S) (N : ℕ), 0 < N → IsCommensurated (S.L.KN N) ∧ ∀ K : Subgroup (GUf E n), IsCompact (K : Set (GUf E n)) →
    IsOpen (K : Set (GUf E n)) → (S.L.KN N).relIndex (T.lv K) ≠ 0

def PPart : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S) (g : GUf E n), ∃ k : GUf E n, g = T.sec (T.j g) * k ∧ (∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w k = 1) ∧
    (∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w k = comp w g) ∧ ∀ h, T.sec h * k = k * T.sec h

def HasEigOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S) (V : Type) [AddCommGroup V] [Module ℂ V] (ξ : Representation ℂ (GL (Fin n) E × ℚˣ) V) (Φ : GUf E n → V),
  (∀ (γ : Gam0 E n) g, Φ (rat γ * g) = ξ γ (Φ g)) →
  (∀ k : GUf E n, (∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w k = 1) → (∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w k ∈ KGL w (n := n)) →
    ∀ g, Φ (g * k) = Φ g) →
  (∃ g₀, Φ g₀ ≠ 0 ∧ ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w g₀ ∈ KGL w (n := n)) →
  ∀ K₀ : Subgroup S.G.GAf, IsCommensurated K₀ → (∀ k ∈ K₀, ∀ h, Φ (T.sec (h * k)) = Φ (T.sec h)) →
  ∀ (J : Type) (ψ : J → S.G.GAf → ℂ) (θ : J → ℂ) (e : S.G.GAf → ℂ), (∀ j, ψ j ∈ Hecke ℂ K₀) → e ∈ Hecke ℂ K₀ →
    hAct K₀ e (fun h => Φ (T.sec h)) = (fun h => Φ (T.sec h)) →
    (∀ j, hAct K₀ (ψ j) (fun h => Φ (T.sec h)) = θ j • fun h => Φ (T.sec h)) →
  Spc.HasEig S.G (V := V) ξ K₀ ψ θ e

end UpperTheory.Gal.W2.Seed
end
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed.LatticeTensorCoordinates

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

private lemma exists_int_multiple (x : Matrix (Fin n) (Fin n) E) :
    ∃ (m : ℤ) (y : Matrix (Fin n) (Fin n) (𝓞 E)), m ≠ 0 ∧ y.map (algebraMap (𝓞 E) E) = (m : ℚ) • x := by
  classical
  obtain ⟨m, hm, hs⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image (fun ij : Fin n × Fin n => x ij.1 ij.2))
  have h : ∀ i j, ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = (m : ℚ) • x i j := by
    intro i j
    have h1 := hs (x i j) (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)
    have h2 : m • x i j = (m : ℚ) • x i j := by
      simp [zsmul_eq_mul, Algebra.smul_def]
    rw [h2] at h1
    exact ⟨IsIntegralClosure.mk' (𝓞 E) _ h1, IsIntegralClosure.algebraMap_mk' _ _ _⟩
  choose y hy using h
  refine ⟨m, Matrix.of y, hm, ?_⟩
  ext i j
  simp [hy]

private lemma beta_rep (rep : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ (ℚ ⊗[ℤ] (Fin n → 𝓞 E)))
    (hrep : ∀ (x : Matrix (Fin n) (Fin n) (𝓞 E)) (v : Fin n → 𝓞 E),
      rep (x.map (algebraMap (𝓞 E) E)) ((1 : ℚ) ⊗ₜ[ℤ] v) = (1 : ℚ) ⊗ₜ[ℤ] (x *ᵥ v))
    (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℚ] (Fin n → E))
    (hβ : ∀ (v : Fin n → 𝓞 E) i, β (1 ⊗ₜ v) i = (v i : E))
    (x : Matrix (Fin n) (Fin n) E) (z : ℚ ⊗[ℤ] (Fin n → 𝓞 E)) : β (rep x z) = x *ᵥ β z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), mulVec_add, ha, hb]
  | tmul q v =>
    have hq : q ⊗ₜ[ℤ] v = q • ((1 : ℚ) ⊗ₜ[ℤ] v) := by
      rw [TensorProduct.smul_tmul']; simp
    obtain ⟨m, y, hm, hy⟩ := exists_int_multiple x
    have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm
    have key : (m : ℚ) • β (rep x (1 ⊗ₜ v)) = (m : ℚ) • (x *ᵥ β (1 ⊗ₜ v)) := by
      have e1 : (m : ℚ) • β (rep x (1 ⊗ₜ v)) = β (rep ((m : ℚ) • x) (1 ⊗ₜ v)) := by
        rw [map_smul, LinearMap.smul_apply, map_smul]
      have e2 : (m : ℚ) • (x *ᵥ β (1 ⊗ₜ v)) = ((m : ℚ) • x) *ᵥ β (1 ⊗ₜ v) := by
        rw [smul_mulVec]
      rw [e1, e2, ← hy, hrep]
      ext i
      rw [hβ]
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
      rw [show ((∑ k, y i k * v k : 𝓞 E) : E) = ∑ k, ((y i k : 𝓞 E) : E) * (v k : E) by
        simp]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hβ]
    have h3 : β (rep x (1 ⊗ₜ v)) = x *ᵥ β (1 ⊗ₜ v) := smul_right_injective _ hmq key
    rw [hq, map_smul, map_smul, map_smul, mulVec_smul, h3]

private def nu (R : Type) [CommRing R] [Algebra ℚ R] (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℚ] (Fin n → E)) :
    R ⊗[ℚ] (ℚ ⊗[ℤ] (Fin n → 𝓞 E)) ≃+ (Fin n → R ⊗[ℚ] E) :=
  ((TensorProduct.congr (LinearEquiv.refl ℚ R) β).trans
    (TensorProduct.piRight ℚ ℚ R (fun _ : Fin n => E))).toAddEquiv

private lemma nu_tmul (R : Type) [CommRing R] [Algebra ℚ R]
    (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℚ] (Fin n → E)) (r : R) (z : ℚ ⊗[ℤ] (Fin n → 𝓞 E)) (i : Fin n) :
    nu R β (r ⊗ₜ z) i = r ⊗ₜ (β z i) := by
  simp [nu]

private lemma actOn_tmul {R : Type} [CommRing R] [Algebra ℚ R]
    (rep : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ (ℚ ⊗[ℤ] (Fin n → 𝓞 E)))
    (r r' : R) (x : Matrix (Fin n) (Fin n) E) (z : ℚ ⊗[ℤ] (Fin n → 𝓞 E)) :
    actOn rep R (r ⊗ₜ x) (r' ⊗ₜ z) = (r * r') ⊗ₜ rep x z := by
  unfold actOn
  erw [Algebra.TensorProduct.lift_tmul]
  show r • (LinearMap.baseChange R (rep x)) (r' ⊗ₜ z) = _
  rw [LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul]

private lemma nu_act {R : Type} [CommRing R] [Algebra ℚ R]
    (μ : R ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) (hμ : IsMu μ)
    (rep : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ (ℚ ⊗[ℤ] (Fin n → 𝓞 E)))
    (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℚ] (Fin n → E))
    (hr : ∀ x z, β (rep x z) = x *ᵥ β z)
    (y : R ⊗[ℚ] Matrix (Fin n) (Fin n) E) (v : R ⊗[ℚ] (ℚ ⊗[ℤ] (Fin n → 𝓞 E))) :
    nu R β (actOn rep R y v) = μ y *ᵥ nu R β v := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, add_mulVec, ha, hb]
  | tmul r x =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), mulVec_add, ha, hb]
    | tmul r' z =>
      ext1 i
      rw [actOn_tmul, nu_tmul, hr]
      simp only [Matrix.mulVec, dotProduct, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hμ r x i k, nu_tmul, Algebra.TensorProduct.tmul_mul_tmul]

private lemma nu_mem {p : ℕ} (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℚ] (Fin n → E))
    (hβ : ∀ (v : Fin n → 𝓞 E) i, β (1 ⊗ₜ v) i = (v i : E))
    (v : AfP p ⊗[ℚ] (ℚ ⊗[ℤ] (Fin n → 𝓞 E))) :
    v ∈ AddSubgroup.closure {z : AfP p ⊗[ℚ] (ℚ ⊗[ℤ] (Fin n → 𝓞 E)) |
        ∃ (a : AfP p) (x : Fin n → 𝓞 E), IsIntAf a ∧ z = a ⊗ₜ ((1 : ℚ) ⊗ₜ x)} ↔
      ∀ i, nu (AfP p) β v i ∈ OHat p E := by
  classical
  constructor
  · intro h i
    induction h using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, x, ha, rfl⟩ := hz
      exact AddSubgroup.subset_closure ⟨a, x i, ha, by rw [nu_tmul, hβ]⟩
    | zero => simpa using zero_mem _
    | add a b _ _ h1 h2 =>
      simpa only [map_add, Pi.add_apply] using add_mem h1 h2
    | neg a _ h => rw [map_neg]; exact neg_mem h
  · intro h
    have hs : ∀ i, ∀ w ∈ OHat p E, (nu (AfP p) β).symm (Pi.single i w) ∈
        AddSubgroup.closure {z : AfP p ⊗[ℚ] (ℚ ⊗[ℤ] (Fin n → 𝓞 E)) |
          ∃ (a : AfP p) (x : Fin n → 𝓞 E), IsIntAf a ∧ z = a ⊗ₜ ((1 : ℚ) ⊗ₜ x)} := by
      intro i w hw
      induction hw using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, x, ha, rfl⟩ := hz
        refine AddSubgroup.subset_closure ⟨a, Pi.single i x, ha, ?_⟩
        rw [AddEquiv.symm_apply_eq]
        funext j
        rw [nu_tmul, hβ]
        by_cases hj : j = i
        · subst hj; simp
        · simp [hj]
      | zero => simpa using zero_mem _
      | add a b _ _ h1 h2 => rw [Pi.single_add, map_add (f := _)]; exact add_mem h1 h2
      | neg a _ h => rw [Pi.single_neg, map_neg]; exact neg_mem h
    have hv : v = ∑ i, (nu (AfP p) β).symm (Pi.single i (nu (AfP p) β v i)) := by

      rw [← map_sum, Finset.univ_sum_single]; simp
    rw [hv]
    exact sum_mem fun i _ => hs i _ (h i)

end UpperTheory.Gal.W2.Seed.LatticeTensorCoordinates

namespace UpperTheory.Gal.W2.Seed

open LatticeTensorCoordinates

theorem pLatCoord :
    RepLaws → LatCoord := by
  intro _ E _ _ _ A n p _ S μ hμ
  obtain ⟨β, hβ⟩ := pRepEx E n
  have hr : ∀ x z, β (S.L.rep x z) = x *ᵥ β z := beta_rep S.L.rep S.L_rep β hβ
  refine ⟨nu (AfP p) β, ?_, ?_, ?_⟩
  · intro r v i
    exact (nu_tmul (AfP p) β r _ i).trans (congrArg (fun t => r ⊗ₜ[ℚ] t) (hβ v i))
  · intro h v
    exact nu_act μ hμ S.L.rep β hr (S.mx h) v
  · intro v
    exact nu_mem β hβ v

end UpperTheory.Gal.W2.Seed
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

private lemma one_tmul_smul_eq_add_of_algebraMap_eq_add {M R : Type} [AddCommGroup M] [CommRing R] [Algebra ℚ R] (r : R) (q : ℚ) (y : M) :
    (r ⊗ₜ[ℚ] (q ⊗ₜ[ℤ] y : ℚ ⊗[ℤ] M)) = (q • r) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] y : ℚ ⊗[ℤ] M) := by
  rw [TensorProduct.smul_tmul, TensorProduct.smul_tmul']
  simp

theorem UpperTheory.Gal.W2.Seed.pVecCoord :
    LatCoord → EvEx → VecCoord := by
  intro hLat hEv E _ _ _ A n p _ S T
  obtain ⟨ν, hν1, hν2, hν3⟩ := hLat E A n p S T.μ T.mu
  choose ev hev using fun (w : Plc E) (hw : (p : 𝓞 E) ∉ w.asIdeal) => hEv p E T.toAdT w hw
  let co : ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → (AfP p ⊗[ℚ] VQ S.D →+ (Fin n → w.adicCompletion E)) := fun w hw =>
    { toFun := fun v i => ev w hw (ν v i)
      map_zero' := by ext i; simp
      map_add' := fun x y => by ext i; simp }
  let vec : ∀ w : Plc E, AfP p ⊗[ℚ] VQ S.D →+ (Fin n → w.adicCompletion E) := fun w =>
    if hw : (p : 𝓞 E) ∉ w.asIdeal then co w hw else 0
  have hvec : ∀ w (hw : (p : 𝓞 E) ∉ w.asIdeal) v i, vec w v i = ev w hw (ν v i) := fun w hw v i => by
    simp only [vec, dif_pos hw]; rfl
  have hE : ∀ w (hw : (p : 𝓞 E) ∉ w.asIdeal) (c : 𝓞 E), ev w hw ((1 : AfP p) ⊗ₜ[ℚ] (c : E)) = algebraMap (𝓞 E) (w.adicCompletion E) c := by
    intro w hw c
    rw [← T.Φ_E, hev]
    rfl
  have hν4 : ∀ (r : AfP p) (q : ℚ) (y : Fin n → 𝓞 E) i, ν (r ⊗ₜ[ℚ] ((q ⊗ₜ[ℤ] (y : S.D.La) : VQ S.D))) i = (q • r) ⊗ₜ[ℚ] (y i : E) := by
    intro r q y i
    exact (congrArg (fun z => ν z i) (one_tmul_smul_eq_add_of_algebraMap_eq_add (M := S.D.La) r q y)).trans (hν1 _ y i)
  refine ⟨vec, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v h
    apply ν.injective
    rw [map_zero]
    funext i
    obtain ⟨x, hx⟩ := T.Φ_surj (ν v i)
    rw [Pi.zero_apply, ← hx, T.Φ_ker]
    intro w hw
    have := congrFun (h w hw) i
    rw [hvec w hw, ← hx, hev] at this
    exact this
  · intro v
    rw [hν3]
    constructor
    · intro h w hw i
      obtain ⟨x, hx⟩ := T.Φ_surj (ν v i)
      have := (T.Φ_int x).1 (hx ▸ h i) w hw
      rw [hvec w hw, ← hx, hev]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 this
    · intro h i
      obtain ⟨x, hx⟩ := T.Φ_surj (ν v i)
      rw [← hx, T.Φ_int]
      intro w hw
      have := h w hw i
      rw [hvec w hw, ← hx, hev] at this
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 this
  · intro y hy
    let x : Fin n → Af E := fun i => ⟨fun w => y w i, Filter.Eventually.of_forall fun w => hy w i⟩
    refine ⟨ν.symm (fun i => T.Φ (x i)), fun w hw => ?_⟩
    funext i
    rw [hvec w hw, ν.apply_symm_apply, hev]
    rfl
  · intro w hw y i
    rw [hvec w hw, ← hE w hw]
    congr 1
    exact hν1 1 y i
  · intro w hw g v
    funext i
    rw [hvec w hw, hν2, T.j_mx, RingHom.map_mulVec]
    have hG : GeneralLinearGroup.map (pLoc E w) T.a * comp w g * (GeneralLinearGroup.map (pLoc E w) T.a)⁻¹ =
        GeneralLinearGroup.map (pLoc E w) (T.a * mat g * T.a⁻¹) := by
      simp [UpperTheory.Gal.CertificateRingHomMap.comp]
    have hM : (((T.a * mat g * T.a⁻¹ : GL (Fin n) (Af E)).val).map T.Φ).map (ev w hw) =
        (GeneralLinearGroup.map (pLoc E w) (T.a * mat g * T.a⁻¹)).val := by
      exact Matrix.ext fun a b => hev w hw _
    have hV : (ev w hw) ∘ (ν v) = vec w v := funext fun k => (hvec w hw v k).symm
    rw [hM, hV, hG]
  · intro w hw c v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), smul_add]
    | tmul r u =>
      induction u using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [TensorProduct.tmul_add, map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), smul_add]
      | tmul q y =>
        let y' : Fin n → 𝓞 E := y
        have key : UpperTheory.Gal.Int.Geo.mulF S.D c (r ⊗ₜ[ℚ] (q ⊗ₜ[ℤ] y)) =
            r ⊗ₜ[ℚ] ((q ⊗ₜ[ℤ] ((c • y' : Fin n → 𝓞 E) : S.D.La) : VQ S.D)) := by
          simp only [UpperTheory.Gal.Int.Geo.mulF, LinearMap.baseChange_tmul, actQ]
          rfl
        funext i
        have e2 : ν (r ⊗ₜ[ℚ] (q ⊗ₜ[ℤ] y)) i = (q • r) ⊗ₜ[ℚ] (y' i : E) := hν4 r q y' i
        have e3 : (((c • y') i : 𝓞 E) : E) = (c : E) * (y' i : E) := by simp [Pi.smul_apply]
        rw [key, Pi.smul_apply, hvec w hw, hvec w hw, hν4, e2, e3, ← hE w hw, smul_eq_mul, ← map_mul (ev w hw),
          Algebra.TensorProduct.tmul_mul_tmul, one_mul]
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open GlobalTheory.LFun (KGL)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.W2.Seed

theorem pEvEx : EvEx := by
  intro p E _ _ _ T w hw
  have hk : RingHom.ker T.Φ ≤ RingHom.ker (pLoc E w) := by
    intro x hx
    exact RingHom.mem_ker.2 (((T.Φ_ker x).1 (RingHom.mem_ker.1 hx)) w hw)
  refine ⟨RingHom.liftOfSurjective T.Φ T.Φ_surj ⟨pLoc E w, hk⟩, fun x => ?_⟩
  exact RingHom.liftOfRightInverse_comp_apply _ _ _ ⟨pLoc E w, hk⟩ x

end UpperTheory.Gal.W2.Seed
end
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

private theorem mem_GLint_of_entries {K : Type} [Field K] {n : ℕ} (O : Subring K) (g : GL (Fin n) K)
    (h1 : ∀ a b, g.val a b ∈ O) (h2 : ∀ a b, (g⁻¹).val a b ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have inj : Function.Injective (O.subtype.mapMatrix (m := Fin n)) :=
    fun A B h => by ext i j; exact congrFun (congrFun h i) j
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨g.val i j, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
  have hA : O.subtype.mapMatrix A = g.val := rfl
  have hB : O.subtype.mapMatrix B = (g⁻¹).val := rfl
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hA, hB, map_one, Units.mul_inv]
  · rw [map_mul, hA, hB, map_one, Units.inv_mul]

theorem UpperTheory.Gal.W2.Seed.pIntCof :
    IntCof := by
  intro E _ _ n a
  have key : ∀ x : Af E, ∀ᶠ w : Plc E in Filter.cofinite, pLoc E w x ∈ w.adicCompletionIntegers E :=
    fun x => x.2
  have h1 := Filter.eventually_all.2 (fun i => Filter.eventually_all.2 (fun j => key (a.val i j)))
  have h2 := Filter.eventually_all.2 (fun i => Filter.eventually_all.2 (fun j => key ((a⁻¹).val i j)))
  filter_upwards [h1, h2] with w ha hb
  refine mem_GLint_of_entries (w.adicCompletionIntegers E).toSubring _ (fun i j => ha i j) (fun i j => ?_)
  rw [← map_inv]
  exact hb i j
end
