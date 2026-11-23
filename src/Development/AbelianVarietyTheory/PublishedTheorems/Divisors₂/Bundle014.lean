module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
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
import Mathlib.Tactic.Polynomial.Basic
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.Published

def ComplementaryThetaInert : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n a a' r : ℕ) (V : Spc F E a) (V' : Spc F E a') (W : Spc F E (a + a')) (M : Model σ V W) (M' : Model σ V' W)
      (ψ : AddChar (AF F) ℂ) (χV χW χV' χW' : Chr F E) (om : Rep σ V W) (om' : Rep σ V' W),
      a + a' = 2 * n → a = a' + 2 * r → 0 < r → 0 < a' → IsStd ψ →
      (∀ i j, σ (V.J j i) = V.J i j) → V.J.det ≠ 0 → (∀ i j, σ (V'.J j i) = V'.J i j) → V'.J.det ≠ 0 →
      (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χV a →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χV' a' →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW (a + a') →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW' (a + a') →
      IsHecke F E χV → IsHecke F E χV' → IsHecke F E χW → IsHecke F E χW' →
      M.IsWeil ψ χV χW om → M'.IsWeil ψ χV' χW' om' →
    ∀ v : Pl (F := F), IsField (Fv F v ⊗[F] E) →
      (∃ Cy : Matrix (Fin (a + a')) (Fin n) (Fv F v ⊗[F] E),
        IsLagr (Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ) (JR (Fv F v) W.J) Cy) →
      (∃ P : Matrix (Fin a) (Fin a' ⊕ (Fin r ⊕ Fin r)) (Fv F v ⊗[F] E),
        Pᵀ * JR (F := F) (Fv F v) V.J * P.map (sigR (Fv F v) σ) =
          (Matrix.fromBlocks (JR (Fv F v) V'.J) 0 0 (Matrix.fromBlocks 0 1 1 0) :
            Matrix (Fin a' ⊕ (Fin r ⊕ Fin r)) (Fin a' ⊕ (Fin r ⊕ Fin r)) (Fv F v ⊗[F] E))) →
      (∀ z : (AE F E)ˣ, At (evFin F v) ((z : AE F E) - 1) → χV z = χV' z ∧ χW z = 1 ∧ χW' z = 1) →
      augAt om' v ≠ SB _ ∧
      (∀ N : Submodule ℂ (_ → ℂ), augAt om' v ≤ N → N ≤ SB _ → (∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ N, ∀ φ₁ ∈ SB _,
        Acts (evFin F v) (om' (1, h)) φ φ₁ → φ₁ ∈ N) → N = augAt om' v ∨ N = SB _) ∧
      ∃ p : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (((Fin a' × Fin (a + a') → Fv F v) → ℂ) ⧸ augAt om' v),
        (SB _).map p = (SB _).map (augAt om' v).mkQ ∧ augAt om v ≤ LinearMap.ker p ∧
        ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB _, ∀ φ' ∈ SB _, ∀ φ₁ ∈ SB _, ∀ φ₁' ∈ SB _,
          Acts (evFin F v) (om (1, h)) φ φ₁ → Acts (evFin F v) (om' (1, h)) φ' φ₁' →
          p φ = (augAt om' v).mkQ φ' → p φ₁ = (augAt om' v).mkQ φ₁'

end GlobalTheory.Published

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.Published

def ThetaSubInf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (om : Rep σ X W) (N : Submodule ℂ (SInf F (Fin n × Fin d))) : Prop :=
  N ≤ M.Pol ψ τ ∧
  (∀ γ ∈ Lines σ X, ∀ f ∈ M.Pol ψ τ, ∀ f₁ : SInf F (Fin n × Fin d),
    ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ → f₁ ∈ N) ∧
  (∀ k ∈ KInf σ X τ, ∀ f ∈ M.Pol ψ τ, ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (k, 1)) f f₁ → f₁ - f ∈ N) ∧
  (∀ γ ∈ Lines σ W, ∀ f ∈ N, ∀ f₁ : SInf F (Fin n × Fin d),
    ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → f₁ ∈ N) ∧
  ∀ k ∈ KInf σ W τ, ∀ f ∈ N, ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₁ → f₁ ∈ N

def HoweDualityReal : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
        (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ _), StrictMono N → (∀ i, ThetaSubInf M ψ τ om (N i)) → m ≤ L) ∧
        ∀ N N', ThetaSubInf M ψ τ om N → ThetaSubInf M ψ τ om N' → N ≠ M.Pol ψ τ → N' ≠ M.Pol ψ τ → N ⊔ N' ≠ M.Pol ψ τ

end GlobalTheory.Published

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct

namespace GlobalTheory.Published

section Local

variable {G H Y V T : Type} [Group G] [Group H] [TopologicalSpace Y] [AddCommGroup V] [Module ℂ V] [AddCommGroup T]
  [Module ℂ T]

def IsLeftHom (om : G × H →* Module.End ℂ (Y → ℂ)) (π : Representation ℂ G V) (f : SB Y →ₗ[ℂ] V) : Prop :=
  ∀ (g : G) (φ φ₁ : SB Y), (φ₁ : Y → ℂ) = om (g, 1) φ → f φ₁ = π g (f φ)

def IsPairHom (om : G × H →* Module.End ℂ (Y → ℂ)) (π : Representation ℂ G V) (τ : Representation ℂ H T)
    (f : SB Y →ₗ[ℂ] V ⊗[ℂ] T) : Prop :=
  ∀ (g : G) (h : H) (φ φ₁ : SB Y), (φ₁ : Y → ℂ) = om (g, h) φ → f φ₁ = TensorProduct.map (π g) (τ h) (f φ)

def IsBigTheta (om : G × H →* Module.End ℂ (Y → ℂ)) (π : Representation ℂ G V) (Θ : Representation ℂ H T)
    (p : SB Y →ₗ[ℂ] V ⊗[ℂ] T) : Prop :=
  IsPairHom om π Θ p ∧ Function.Surjective p ∧ ∀ φ, p φ = 0 ↔ ∀ f, IsLeftHom om π f → f φ = 0

def HoweDualityFor [TopologicalSpace G] [TopologicalSpace H] (om : G × H →* Module.End ℂ (Y → ℂ)) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), π.IsIrreducible → GlobalTheory.PRep.IsAdmissible π →
    (∃ (T : Type) (_ : AddCommGroup T) (_ : Module ℂ T) (Θ : Representation ℂ H T) (p : SB Y →ₗ[ℂ] V ⊗[ℂ] T),
      IsBigTheta om π Θ p ∧ GlobalTheory.PRep.IsSmooth Θ ∧ IsFiniteLength (MonoidAlgebra ℂ H) Θ.asModule ∧
        ∀ N N' : Subrepresentation Θ, IsCoatom N → IsCoatom N' → N = N') ∧
    ∀ (T : Type) [AddCommGroup T] [Module ℂ T] (τ : Representation ℂ H T), τ.IsIrreducible → GlobalTheory.PRep.IsSmooth τ →
      ∀ f : SB Y →ₗ[ℂ] V ⊗[ℂ] T, IsPairHom om π τ f → f ≠ 0 →
        (∀ f' : SB Y →ₗ[ℂ] V ⊗[ℂ] T, IsPairHom om π τ f' → ∃ a : ℂ, f' = a • f) ∧
        ∀ (V' : Type) [AddCommGroup V'] [Module ℂ V'] (π' : Representation ℂ G V'), π'.IsIrreducible →
          GlobalTheory.PRep.IsAdmissible π' → ∀ f' : SB Y →ₗ[ℂ] V' ⊗[ℂ] T, IsPairHom om π' τ f' → f' ≠ 0 → Nonempty (π.Equiv π')

end Local

def HoweDualityUnitary : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (δ : E), IsQuad c δ →
  ∀ ψ : AddChar k ℂ, Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 →
  ∀ (n d : ℕ) (ξ : E) (JA : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) E),
    IsHerm c JA → ξ ≠ 0 → (∀ i j, c (ξ * JB j i) = -(ξ * JB i j)) → JB.det ≠ 0 →
  ∀ χA χB : Eˣ →* Circle, Continuous χA → Continuous χB → ResEtaPow (R := k) ⊥ χA n → ResEtaPow (R := k) ⊥ χB d →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp c ξ JA JB) κ) (om : UG c JA × UG c JB →* Module.End ℂ ((κ → k) → ℂ)),
    IsUWeilPair c (sbClass k) ψ ξ JA JB co χA χB om →
    HoweDualityFor om ∧ HoweDualityFor (om.comp (MulEquiv.prodComm (M := UG c JB) (N := UG c JA)).toMonoidHom)

def ThetaSub {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (om : Rep σ X W) (v : Pl (F := F)) (N : Submodule ℂ ((Fin n × Fin d → Fv F v) → ℂ)) : Prop :=
  augAt om v ≤ N ∧ N ≤ SB _ ∧
    ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ N, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h)) φ φ₁ → φ₁ ∈ N

end GlobalTheory.Published

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.Published

def WeilRepresentationExists : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → W.IsSkew σ B r' s' → ∀ M : Model σ X W, M.IsGood B.ψ →
    ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → ∃ om, M.IsWeil B.ψ χX χW om

end GlobalTheory.Published

end
end

section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt

namespace GlobalTheory.Published

def ArFormExists : Prop := ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
  ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p), ∃ Φ, IsArFun L D Φ

end GlobalTheory.Published
end
end

section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt

namespace GlobalTheory.Published

def VolGe : Prop := ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
  ∀ (L : HermLB p) (a : ℝ), NefFib L → L.SemiPos D → L.IsSelfInter a → (a : EReal) ≤ arVol L D

end GlobalTheory.Published
end
end

section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt

namespace GlobalTheory.Published

def VolNef : Prop := ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
  ∀ (L : HermLB p) (a : ℝ), L.IsNef D → L.IsSelfInter a → arVol L D = (a : EReal)

end GlobalTheory.Published
end
end

section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts

namespace GlobalTheory.HermLB

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

def Isometric (L M : HermLB p) : Prop :=
  ∃ w : LB.Iso L.B M.B, w.IsGen ∧ ∀ (σ : k →+* ℂ) (a : M.B.ι) (b : L.B.ι) (y : CxPts p σ),
    y ∈ ptsIn p σ (M.B.U a) → y ∈ ptsIn p σ (L.B.U b) →
      (M.φ σ).φ a y = (L.φ σ).φ b y + Real.log (‖ev p σ _ (w.s (a, b)).val y‖ ^ 2)
private theorem res_res_lemma {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)ˣ) :
    res h' (res h a) = res (h'.trans h) a := by
  ext
  change (X.presheaf.map (homOfLE h').op).hom ((X.presheaf.map (homOfLE h).op).hom a.val) =
    (X.presheaf.map (homOfLE (h'.trans h)).op).hom a.val
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl
private theorem isGen_iso_self_of_isLB (B : LB X) (hB : B.IsLB) :
    (⟨fun c => B.g c.1 c.2⟩ : LB.Iso B B).IsGen := by
  obtain ⟨-, -, hc⟩ := hB
  rintro ⟨a, b⟩ ⟨a', b'⟩
  have e1 := congrArg (res (fun x hx => by simp only [Opens.mem_inf] at hx ⊢; tauto :
    (B.U a ⊓ B.U b) ⊓ (B.U a' ⊓ B.U b') ≤ _)) (hc a a' b')
  have e2 := congrArg (res (fun x hx => by simp only [Opens.mem_inf] at hx ⊢; tauto :
    (B.U a ⊓ B.U b) ⊓ (B.U a' ⊓ B.U b') ≤ _)) (hc a b b')
  simp only [map_mul, res_res_lemma] at e1 e2
  dsimp only [LB.div]
  refine (eq_mul_inv_of_mul_eq e2).trans ?_
  rw [← e1]
  exact mul_right_comm _ _ _
private theorem iso_phi_eq_add_log_normSq_transition {B : LB X} (hB : B.IsLB) (φ ψ : ∀ σ : k →+* ℂ, Weight p σ B)
    (h : ∀ σ a, ∀ y ∈ ptsIn p σ (B.U a), (ψ σ).φ a y = (φ σ).φ a y) (σ : k →+* ℂ) (a b : B.ι)
    (y : CxPts p σ) (ha : y ∈ ptsIn p σ (B.U a)) (hb : y ∈ ptsIn p σ (B.U b)) :
    (ψ σ).φ a y = (φ σ).φ b y + Real.log (‖ev p σ (B.U a ⊓ B.U b) (B.g a b).val y‖ ^ 2) := by
  rw [h σ a y ha, (φ σ).trans a b y ha hb]
  exact (sub_add_cancel _ _).symm

theorem isometric_of_eqOn {B : LB X} {hB : B.IsLB} {φ ψ : ∀ σ : k →+* ℂ, Weight p σ B} {h₁ h₂ h₃ h₄}
    (h : ∀ σ a, ∀ y ∈ ptsIn p σ (B.U a), (ψ σ).φ a y = (φ σ).φ a y) :
    Isometric (p := p) ⟨B, hB, φ, h₁, h₂⟩ ⟨B, hB, ψ, h₃, h₄⟩ :=
  ⟨⟨fun c => B.g c.1 c.2⟩, isGen_iso_self_of_isLB B hB, fun σ a b y ha hb => iso_phi_eq_add_log_normSq_transition hB φ ψ h σ a b y ha hb⟩

theorem Isometric.refl (L : HermLB p) : L.Isometric L := by
  obtain ⟨B, hB, φ, h₁, h₂⟩ := L
  exact isometric_of_eqOn fun _ _ _ _ => rfl

def raise (M : HermLB p) (u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) (hu : ∀ σ y, CInfAt (u σ) y)
    (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) : HermLB p where
  B := M.B
  isLB := M.isLB
  φ σ := (M.φ σ).addFn (u σ)
  cInf σ := (M.cInf σ).addFn (hu σ)
  conj σ σ' c y y' h hy := congrArg₂ (· + ·) (M.conj σ σ' c y y' h hy)
    (hc σ σ' PUnit.unit y y' h mem_ptsIn_top)

end GlobalTheory.HermLB

namespace GlobalTheory.Published

def ArExists : Prop := ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
  (∀ L : HermLB p, ∃ h, L.IsArithHeight h) ∧
  ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p), (∃ Φ, IsArFun L D Φ) ∧ ∃ Ψ, IsGeoFun L D Ψ

def ArChange : Prop := ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
  ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) (hu : ∀ σ y, CxPts.CInfAt (u σ) y)
    (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) (Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ),
    IsArFun (fun o : Option ι => o.elim (fnB u hu hc) L) D Φ → ∀ n : ι → ℤ,
      Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) = 1 / 2 * chInt (comb L n) D u

def ArShift : Prop := ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
  ∀ (L : HermLB p) (a t : ℝ), L.IsSelfInter a →
    (L.shift (fun _ => t) fun _ => rfl).IsSelfInter (a + ((D : ℝ) + 1) * t * gdeg L D)

def ArMix : Prop := ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (D : ℕ),
  IsArithVar p D → ∀ (ι : Type) [Fintype ι] (M : HermLB p) (L : ι → HermLB p) (Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ),
    IsArFun (fun o : Option ι => o.elim M L) D Φ → ∀ (n : ι → ℤ) (h : X → ℝ), (comb L n).IsArithHeight h →
    ∀ (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), (comb L n).ArchIntegrable M D hr ∧
      Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) =
        ∑ᶠ z, ((M.div hr).mult z : ℝ) * h z - (comb L n).archInt M D hr

def ArProj : Prop := ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k)
  (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X →
    π.residueDegree (genericPoint Y) ≠ 0 →
    (∀ (L : HermLB p) (a : ℝ), L.IsSelfInter a →
      (L.pull π hπ).IsSelfInter ((π.residueDegree (genericPoint Y) : ℝ) * a)) ∧
    ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ), IsArFun L D Φ →
      IsArFun (fun i => (L i).pull π hπ) D ((π.residueDegree (genericPoint Y) : ℝ) • Φ)

def ArIso : Prop := ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
  (∀ (L M : HermLB p) (h : X → ℝ), L.Isometric M → L.IsArithHeight h → M.IsArithHeight h) ∧
  ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ), IsArFun L D Φ →
    (∀ i, (L i).IsSelfInter (Φ (MvPolynomial.X i ^ (D + 1)))) ∧
    (∀ M : ι → HermLB p, (∀ i, (L i).Isometric (M i)) → IsArFun M D Φ) ∧
    ∀ (κ : Type) [Fintype κ] (M : κ → HermLB p) (A : κ → ι → ℤ), (∀ j, (comb L (A j)).Isometric (M j)) →
      IsArFun M D (Φ ∘ₗ (aeval fun j => lin fun i => (A j i : ℝ) : MvPolynomial κ ℝ →ₐ[ℝ] MvPolynomial ι ℝ).toLinearMap)

def ArMetric : Prop := ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
  ∀ (ι : Type) [Fintype ι] (M : HermLB p) (L : ι → HermLB p) (u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ)
    (hu : ∀ σ y, CxPts.CInfAt (u σ) y) (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ')))
    (Φ Φ' : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ), IsArFun (fun o : Option ι => o.elim M L) D Φ →
    IsArFun (fun o : Option ι => o.elim (M.raise u hu hc) L) D Φ' → ∀ n : ι → ℤ,
      (∀ σ, ((comb L n).φ σ).ChernIntegrableOn D Set.univ (u σ)) ∧
      Φ' (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) =
        Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) + 1 / 2 * chInt (comb L n) D u

def ArCalc : Prop := ArExists ∧ ArChange ∧ ArShift ∧ ArMix ∧ ArProj ∧ ArIso ∧ ArMetric

theorem ArCalc.arExists (h : ArCalc) : ArExists := h.1

theorem ArCalc.arChange (h : ArCalc) : ArChange := h.2.1

theorem ArCalc.arShift (h : ArCalc) : ArShift := h.2.2.1

theorem ArCalc.arMix (h : ArCalc) : ArMix := h.2.2.2.1

theorem ArCalc.arProj (h : ArCalc) : ArProj := h.2.2.2.2.1

theorem ArCalc.arIso (h : ArCalc) : ArIso := h.2.2.2.2.2.1

section Consequences

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ} {ι : Type} [Fintype ι]

theorem ArMix.fnB (H : ArMix) (HE : ArExists) (hX : IsArithVar p D) {L : ι → HermLB p}
    {u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} {hu : ∀ σ y, CInfAt (u σ) y}
    {hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))} {Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ}
    (hΦ : IsArFun (fun o : Option ι => o.elim (fnB u hu hc) L) D Φ) (n : ι → ℤ) :
    (∀ σ, ((comb L n).φ σ).ChernIntegrableOn D Set.univ (u σ)) ∧
      Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) = 1 / 2 * chInt (comb L n) D u := by
  haveI : IsLocallyNoetherian X := hX.isLocallyNoetherian
  haveI : Finite (k →+* ℂ) := hX.finite_emb
  obtain ⟨h, hh⟩ := (HE k X p D hX).1 (comb L n)
  have hr1 : IsRatSec (LB.triv X) (fun _ => 1) := by
    intro i j hij
    change (1 : X.functionField) = fnOf _ hij ((1 : Γ(X, ⊤ ⊓ ⊤)ˣ) : Γ(X, ⊤ ⊓ ⊤)) * 1
    simp
  obtain ⟨hI, he⟩ := H k X p D hX ι (ArInt.fnB u hu hc) L Φ hΦ n h hh _ hr1
  have hE : ∀ x, ((ArInt.fnB u hu hc).div hr1).IsEqn x 1 := fun x =>
    (presents_divOfRatSec (LB.isLB_triv X) hr1).isEqn PUnit.unit x trivial
  have hmult : ∀ z, ((ArInt.fnB u hu hc).div hr1).mult z = 0 := fun z => by
    rw [(hE z).mult_eq]
    first
      | exact UnitAt.ord_eq_zero (unitAt_one z)
      | simpa using UnitAt.ord_eq_zero (unitAt_one z)
  have hoff : ∀ σ, offSupp p σ ((ArInt.fnB u hu hc).div hr1) = Set.univ := fun σ =>
    Set.eq_univ_of_forall fun y => mem_offSupp.2 fun hy => hy (hE _)
  have hlog : ∀ σ, logNorm ((ArInt.fnB u hu hc).φ σ) (fun _ : (LB.triv X).ι => 1) =
      fun y => (-1 / 2 : ℝ) * u σ y := by
    intro σ
    funext y
    have hv : ratVal (1 : X.functionField) y = 1 := by
      have e := ratVal_fnOf (mem_ptsIn_top : y ∈ ptsIn p σ ⊤) trivial (1 : Γ(X, ⊤))
      rwa [map_one, ev_one (mem_ptsIn_top : y ∈ ptsIn p σ ⊤)] at e
    simp only [logNorm, Units.val_one, hv, norm_one, Real.log_one, zero_sub]
    change -(u σ y / 2) = (-1 / 2 : ℝ) * u σ y
    ring
  refine ⟨fun σ => ?_, ?_⟩
  · have hi := hI σ
    rw [hoff σ, hlog σ] at hi
    exact ⟨(MeasureTheory.Integrable.const_mul hi.1 (-2)).congr
        (Filter.Eventually.of_forall fun y => by dsimp only; ring),
      (MeasureTheory.Integrable.const_mul hi.2 (-2)).congr
        (Filter.Eventually.of_forall fun y => by dsimp only; ring)⟩
  · rw [he]
    simp only [hmult, Int.cast_zero, zero_mul, finsum_zero, zero_sub]
    unfold HermLB.archInt chInt
    simp only [hoff, hlog, Weight.chernInt_const_mul]
    rw [← mul_finsum]
    ring

end Consequences

theorem arChange_of_arMix (HE : ArExists) (H : ArMix) : ArChange := by
  intro k _ X _ p D hX ι _ L u hu hc Φ hΦ n
  exact (ArMix.fnB H HE hX hΦ n).2

end GlobalTheory.Published
end
end

section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts

namespace GlobalTheory.Published.ChernDegreeComplexModel

variable (Y : Var ℂ)

theorem integrable {L : LB Y.X} (φ : Weight Y.str (RingHom.id ℂ) L) (h : φ.IsCInf) :
    φ.ChernIntegrableOn Y.dim Set.univ (fun _ => 1) := by
  have : CompactSpace (CxPts Y.str (RingHom.id ℂ)) := CxPts.compactSpace _ Y.isProjOver
  let R := AnRead.all Y.str (RingHom.id ℂ) Y.dim
  have hs : φ.IsSmooth R := (Weight.isCInf_iff_isSmooth R).1 h
  have hm := ReciprocityTheory.AnForm.M.mIntegrableCont R.finAtlas (fun _ => φ.locPot)
    (fun _ => Weight.isPotential_locPot hs) (fun _ => 1) continuous_const
  exact ((Weight.chernInt_eq_mInt R h measurable_const).1).2 hm

end GlobalTheory.Published.ChernDegreeComplexModel
end
end
