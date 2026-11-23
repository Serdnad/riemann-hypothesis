module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2026
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle334
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle006
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle075
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1944
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2035
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

open scoped GlobalTheory.VacAny

namespace GlobalTheory.InertSpan

theorem span_translates_vac : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∀ ρ : Matrix (Fin (a + a')) (Fin a') L → Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v)),
      (∀ x (m : SB (Fin a' × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M'.co.rho B.ψ (κ x))
        (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ((ρ x m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ)) →
    ∀ s : SB (Fin a' × Fin (a + a') → Fv F v), (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = G.M'.vac v →
      Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hw _ L _ _ ϖ σL q δ JS JT ψL κ ιS ιT hC ρ hρ s hs
  obtain ⟨-, -, -, -, -, -, -, -, -, hAt, hSurj, -⟩ := hC
  have hunr : PsiUnr B.ψ v := (hT.base.inert v w hw).2.2
  have hvac := hT.geo.hM'.vac v
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (Fin a' × Fin (a + a')) v
  have key : ∀ x, ((ρ x s : SB _) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) =
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (κ x)) (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) :=
    fun x => GlobalTheory.InertAvg.tens_inj v R hR0 (hR _ s.2).1
      ((hρ x s R (hR _ s.2)).symm.trans (GlobalTheory.VacBridge.rho_acts_locCo _ _ v _ (hAt x) _ R (hR _ s.2)))
  have hsurj : ∀ p : (Fin a' × Fin (a + a') → Fv F v) × (Fin a' × Fin (a + a') → Fv F v),
      ∃ x, GlobalTheory.LatVac.locCo G.M'.co v (κ x) = p := by
    intro p
    obtain ⟨x, hx⟩ := hSurj (G.M'.co.e.symm (fun k => GlobalTheory.LatVac.liftV v (p.1 k), fun k => GlobalTheory.LatVac.liftV v (p.2 k)))
      (by
        intro u hu
        rw [← LinearEquiv.map_smul]
        convert G.M'.co.e.symm.map_zero using 2
        ext k
        · exact GlobalTheory.LatVac.at_liftV v (p.1 k) u hu
        · exact GlobalTheory.LatVac.at_liftV v (p.2 k) u hu)
    refine ⟨x, ?_⟩
    rw [hx]
    ext k
    · simp [GlobalTheory.LatVac.locCo, GlobalTheory.LatVac.evFin_liftV]
    · simp [GlobalTheory.LatVac.locCo, GlobalTheory.LatVac.evFin_liftV]
  have hs0 : (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ≠ 0 := hs ▸ hvac.2.1
  have hcond : ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, GlobalTheory.LatVac.psiAt B.ψ v (x * y) = 1) ↔
      x ∈ v.adicCompletionIntegers F := hunr
  have hrange : Set.range (fun p => schr (GlobalTheory.LatVac.psiAt B.ψ v) p (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ)) =
      (SB (Fin a' × Fin (a + a') → Fv F v)).subtype '' Set.range (fun x => ρ x s) := by
    ext f
    constructor
    · rintro ⟨p, rfl⟩
      obtain ⟨x, hx⟩ := hsurj p
      exact ⟨ρ x s, ⟨x, rfl⟩, by rw [Submodule.subtype_apply, key, hx]⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨_, (key x).symm⟩
  rw [eq_top_iff]
  rintro m -
  have hm := GlobalTheory.SchrSpan.mem_span_schr_of_mem_SB F v (GlobalTheory.LatVac.psiAt B.ψ v) _ hcond _ s.2 hs0 _ m.2
  rw [hrange, Submodule.span_image] at hm
  obtain ⟨n, hn, hnm⟩ := hm
  rwa [← Subtype.ext hnm]

end GlobalTheory.InertSpan
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertBridge

theorem weil_normalises_heis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∀ ρ : Matrix (Fin (a + a')) (Fin a') L → Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v)),
      (∀ x (m : SB (Fin a' × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M'.co.rho B.ψ (κ x))
        (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ((ρ x m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ)) →
    ∀ ω : (Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) × Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →*
        Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v))),
      (∀ g h (m : SB (Fin a' × Fin (a + a') → Fv F v)) (φ₁ : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
        φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v) →
        (Acts (evFin F v) (om' (ιS g, ιT h)) (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          ((ω (g, h) m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = φ₁)) →
    ∀ g h x, ω (g, h) * ρ x =
      ρ (((h : GL (Fin (a + a')) L) : Matrix (Fin (a + a')) (Fin (a + a')) L) * x *
        (((g : GL (Fin a') L)⁻¹ : GL (Fin a') L) : Matrix (Fin a') (Fin a') L)) * ω (g, h) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w _ _ L _ _ ϖ σL q δ JS JT ψL κ ιS ιT hC ρ hρ ω hω g h x
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hEq, _, _, _, _⟩ := hC
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (F := F) (Fin a' × Fin (a + a')) v
  have hS := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil'
  have hωA : ∀ (m : SB (Fin a' × Fin (a + a') → Fv F v)), Acts (evFin F v) (om' (ιS g, ιT h))
      (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ((ω (g, h) m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) :=
    fun m => (hω g h m _ (ω (g, h) m).2).2 rfl
  refine LinearMap.ext fun m => ?_
  apply Subtype.ext
  set y := ((h : GL (Fin (a + a')) L) : Matrix (Fin (a + a')) (Fin (a + a')) L) * x *
        (((g : GL (Fin a') L)⁻¹ : GL (Fin a') L) : Matrix (Fin a') (Fin a') L) with hy
  have e1 : om' (ιS g, ιT h) (G.M'.co.rho B.ψ (κ x) (tens (evFin F v) (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) R)) =
      tens (evFin F v) (((ω (g, h) (ρ x m)) : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) R := by
    rw [hρ x m R (hR _ m.2), hωA (ρ x m) R (hR _ (ρ x m).2)]
  have e2 : om' (ιS g, ιT h) (G.M'.co.rho B.ψ (κ x) (tens (evFin F v) (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) R)) =
      tens (evFin F v) (((ρ y (ω (g, h) m)) : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) R := by
    have he : actAB (cA σ) (ιS g, ιT h) (κ x) = κ y := by
      unfold cA
      exact (hEq g h x).trans (congrArg κ hy.symm)
    rw [hS.impl (ιS g, ιT h) (κ x) _ (hR _ m.2).2]
    rw [he, hωA m R (hR _ m.2),
      hρ y (ω (g, h) m) R (hR _ (ω (g, h) m).2)]
  have e := e1.symm.trans e2
  show (((ω (g, h) (ρ x m)) : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) =
    (((ρ y (ω (g, h) m)) : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ)
  funext yv
  set z : (Fin a' × Fin (a + a')) → AF F := fun i => GlobalTheory.LatVac.liftV v (yv i) with hz
  have hza : At (evFin F v) z := fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu
  have hrx : R (0 + z) = R 0 := (hR _ m.2).1 0 z hza
  have hyv : (fun i => evFin F v (((0 : (Fin a' × Fin (a + a')) → AF F) + z) i)) = yv := by
    funext i
    simp only [hz, Pi.add_apply, Pi.zero_apply, zero_add, GlobalTheory.LatVac.evFin_liftV]
  have e' := congrFun e (0 + z)
  simp only [tens] at e'
  rw [hrx, hyv] at e'
  exact mul_right_cancel₀ hR0 e'

end GlobalTheory.InertBridge

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertRhoLaw

theorem darboux_rho_rho {R : Type} [CommRing R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (ψ : AddChar R ℂ) (w w' : W) (Φ : (κ → R) → ℂ) :
    d.rho ψ w (d.rho ψ w' Φ) = ψ (⅟(2 : R) * B w w') • d.rho ψ (w + w') Φ := by
  funext x
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul, map_add (f := _), Prod.fst_add, Prod.snd_add, ← mul_assoc,
    ← AddChar.map_add_eq_mul, add_assoc]
  congr 2
  rw [d.form]
  simp only [add_dotProduct, dotProduct_add]
  have h2 : ⅟(2 : R) + ⅟(2 : R) = 1 := invOf_two_add_invOf_two
  linear_combination (-((d.e w).1 ⬝ᵥ (d.e w').2)) * h2

theorem darboux_rho_zero {R : Type} [CommRing R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (ψ : AddChar R ℂ) (Φ : (κ → R) → ℂ) :
    d.rho ψ 0 Φ = Φ := by
  funext x
  simp [Darboux.rho, schr]

theorem eq_of_tens_eq {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {κ : Type} [Fintype κ] {r : (κ → AF F) → ℂ}
    (hr : ∀ x z, At (evFin F v) z → r (x + z) = r x) (h0 : r 0 ≠ 0) {φ₁ φ₂ : (κ → Fv F v) → ℂ}
    (h : tens (evFin F v) φ₁ r = tens (evFin F v) φ₂ r) : φ₁ = φ₂ := by
  funext y
  set z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i) with hz
  have hza : At (evFin F v) z := by
    intro u hu
    funext i
    exact GlobalTheory.LatVac.at_liftV v _ u hu
  have hrx : r (0 + z) = r 0 := hr 0 z hza
  have hy : (fun i => evFin F v ((0 + z) i)) = y := by
    funext i
    simp only [hz, zero_add, GlobalTheory.LatVac.evFin_liftV]
  have e := congrFun h (0 + z)
  simp only [tens] at e
  rw [hrx, hy] at e
  exact mul_right_cancel₀ h0 e

end GlobalTheory.InertRhoLaw

namespace GlobalTheory.InertRhoLaw

theorem rho_law : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (AE F E))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∀ ρ : Matrix (Fin (a + a')) (Fin a') L → Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v)),
      (∀ x (m : SB (Fin a' × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M'.co.rho B.ψ (κ x))
        (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ((ρ x m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ)) →
    ρ 0 = 1 ∧ ∀ x y, ρ x * ρ y = ψL ((GlobalTheory.Hk3.locH σL δ JS JT x y + σL (GlobalTheory.Hk3.locH σL δ JS JT x y)) / 2) • ρ (x + y) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' _ v w _ _ L _ _ ϖ σL q δ JS JT ψL κ ιS ιT hC ρ hρ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hEq, -, -, -, -, -⟩ := hC
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (F := F) (Fin a' × Fin (a + a')) v
  have hA : ∀ x (m : SB (Fin a' × Fin (a + a') → Fv F v)),
      G.M'.co.rho B.ψ (κ x) (tens (evFin F v) (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) R) =
        tens (evFin F v) ((ρ x m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) R :=
    fun x m => hρ x m R (hR _ m.2)
  have hRi : ∀ x z, At (evFin F v) z → R (x + z) = R x := (hR 0 (Submodule.zero_mem _)).1
  refine ⟨?_, fun x y => ?_⟩
  · refine LinearMap.ext fun m => Subtype.ext ?_
    refine eq_of_tens_eq v hRi hR0 ?_
    rw [← hA 0 m, map_zero, darboux_rho_zero]
    rfl
  · refine LinearMap.ext fun m => Subtype.ext ?_
    refine eq_of_tens_eq v hRi hR0 ?_
    have e1 := hA x (ρ y m)
    have e2 := hA y m
    have e3 := hA (x + y) m
    have hl := darboux_rho_rho G.M'.co B.ψ (κ x) (κ y) (tens (evFin F v) (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) R)
    rw [e2, e1, ← map_add (f := _), e3] at hl
    dsimp only [cA, incM] at hl
    rw [← hEq x y] at hl
    rw [Module.End.mul_apply, hl, LinearMap.smul_apply, Submodule.coe_smul]
    funext z
    simp only [tens, Pi.smul_apply, smul_eq_mul, mul_assoc]

end GlobalTheory.InertRhoLaw

end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp

theorem fdgram_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ G x = (xᴴ * (G.map τ)ᵀ * x)ᵀ := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.transpose_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  simp [RCLike.star_def]
  ring

theorem permM_conj {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ} (e : ι ≃ Fin r) (M : Matrix ι ι ℂ) :
    (permM e)ᴴ * M * permM e = M.submatrix e.symm e.symm := by
  ext a b
  rw [Matrix.mul_apply, ← e.symm.sum_comp]
  simp [permM, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [← e.symm.sum_comp]
  simp

theorem jpq_eq_diagonal (p q : ℕ) :
    Formalism.UG.Jpq p q = Matrix.diagonal (Sum.elim (fun _ : Fin p => (1 : ℂ)) (fun _ : Fin q => -1)) := by
  rw [Formalism.UG.Jpq, ← Matrix.fromBlocks_diagonal, Matrix.diagonal_one, ← Matrix.diagonal_neg]
  rfl

theorem sumElim_sgn {p q r : ℕ} (hcard : r = q + p) (a : Fin r) :
    Sum.elim (fun _ : Fin p => (1 : ℂ)) (fun _ : Fin q => -1)
        (((finCongr hcard).trans (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin q) (Fin p)))) a) =
      -(((sgn q (a : ℕ) : ℝ)) : ℂ) := by
  by_cases h : (a : ℕ) < q
  · have ha : finCongr hcard a = Fin.castAdd p ⟨a, h⟩ := Fin.ext rfl
    have hv : ((finCongr hcard).trans (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin q) (Fin p)))) a =
        Sum.inr ⟨a, h⟩ := by
      rw [Equiv.trans_apply, Equiv.trans_apply, ha, finSumFinEquiv_symm_apply_castAdd]
      rfl
    rw [hv]
    simp [sgn, h]
  · have hlt := a.isLt
    have ha : finCongr hcard a = Fin.natAdd q ⟨(a : ℕ) - q, by omega⟩ := Fin.ext (by simp; omega)
    have hv : ((finCongr hcard).trans (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin q) (Fin p)))) a =
        Sum.inl ⟨(a : ℕ) - q, by omega⟩ := by
      rw [Equiv.trans_apply, Equiv.trans_apply, ha, finSumFinEquiv_symm_apply_natAdd]
      rfl
    rw [hv]
    simp [sgn, h]

theorem exists_frame_of_sig {n p q : ℕ} {Gc : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature Gc p q)
    {A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ} (hA : Aᴴ * Formalism.UG.Jpq p q * A = Gc) :
    ∃ (e : Fin p ⊕ Fin q ≃ Fin n) (x : Matrix (Fin n) (Fin n) ℂ), x.det ≠ 0 ∧ A * x = permM e ∧
      (-(xᴴ * Gc * x))ᵀ = Matrix.diagonal fun a : Fin n => ((sgn q (a : ℕ) : ℝ) : ℂ) := by
  obtain ⟨L, hl, hr⟩ := GlobalTheory.DecompCompare.frame_inv h hA
  obtain ⟨e0, -⟩ := h
  have hcard : n = q + p := by
    have h2 := Fintype.card_congr e0
    simp only [Fintype.card_fin, Fintype.card_sum] at h2
    omega
  set π : Fin n ≃ Fin p ⊕ Fin q :=
    (finCongr hcard).trans (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin q) (Fin p))) with hπ
  have hAx : A * (L * permM π.symm) = permM π.symm := by rw [← Matrix.mul_assoc, hr, Matrix.one_mul]
  refine ⟨π.symm, L * permM π.symm, ?_, hAx, ?_⟩
  · have h1 : (L * permM π.symm) * ((permM π.symm)ᵀ * A) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (permM π.symm), permM_mul_transpose, Matrix.one_mul, hl]
    intro h0
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h2
    exact zero_ne_one h2
  · have key : ∀ y : Matrix (Fin n) (Fin n) ℂ, yᴴ * Gc * y = (A * y)ᴴ * Formalism.UG.Jpq p q * (A * y) := fun y => by
      rw [← hA, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [key, hAx, permM_conj, Equiv.symm_symm, jpq_eq_diagonal, Matrix.submatrix_diagonal_equiv,
      Matrix.diagonal_neg, Matrix.diagonal_transpose]
    congr 1
    funext a
    rw [Function.comp_apply, hπ, sumElim_sgn hcard a, neg_neg]

end GlobalTheory.CovTop.VolUp

namespace GlobalTheory.CovTop.VolUp

theorem exists_ident_frame : ∀ (D : D7) (V : HSp D) (P Q : ℕ), V.SigOK → (∀ τ, V.sig τ = (P, Q)) →
    ∀ A : Frames V, IsFrames V A → ∃ (X₀ : Data D.host.E V.rank) (σ : D.what₂.Tau ≃ X₀.Ψ) (x : Frame X₀.Ψ V.rank)
      (e : ∀ ρ : D.what₂.Tau, Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2 ≃ Fin V.rank),
      X₀.Gm = -(V.gram)ᵀ ∧ (∀ ρ, (σ ρ).1 = tauE D ρ) ∧ IsOrth X₀ x ∧
        IsIdent (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) X₀.Ψ X₀.Gm x σ A e := by
  intro D V P Q hV hs A hA
  choose e x hdet hAx hg using fun ρ => exists_frame_of_sig (hV (tauE D ρ)) (hA ρ)
  have hrk : V.rank = Q + P := by
    have h := hV D.host.φ₀
    rw [hs] at h
    obtain ⟨e0, -⟩ := h
    have h2 := Fintype.card_congr e0
    simp only [Fintype.card_fin, Fintype.card_sum] at h2
    omega
  have hmapT : ∀ ρ, ((-(V.gram)ᵀ).map (tauE D ρ))ᵀ = -(gramAt D V ρ) := fun ρ => by
    ext a b
    simp [gramAt]
  have hgr : ∀ ρ, ReciprocityTheory.ChartRestriction.G.FD.gram (tauE D ρ) (-(V.gram)ᵀ) (x ρ) =
      Matrix.diagonal fun a : Fin V.rank => ((sgn Q (a : ℕ) : ℝ) : ℂ) := fun ρ => by
    have h1 := hg ρ
    simp only [hs] at h1
    rw [fdgram_eq, hmapT, Matrix.mul_neg, Matrix.neg_mul]
    exact h1
  have hin : ∀ ρ, tauE D ρ ∈ Formalism.L2.Pj.cmTypeOfSqrt D := fun ρ => by
    rw [Formalism.L2.Pj.mem_cm_type_iff, Formalism.L2.Theta.tauE_sqrtMinusD]
    exact (D.host.φ₀_mem).symm
  have hmem : ∀ τ : D.host.E →+* ℂ, τ ∈ Formalism.L2.Pj.cmTypeOfSqrt D ↔ ∃ ρ, τ = tauE D ρ := by
    intro τ
    refine ⟨fun h => ?_, fun ⟨ρ, hρ⟩ => hρ ▸ hin ρ⟩
    obtain ⟨ρ, hρ⟩ := (GlobalTheory.CMTypePlaces.mk_tauE_bijective D).2 (InfinitePlace.mk τ)
    rcases InfinitePlace.mk_eq_iff.1 hρ with h' | h'
    · exact ⟨ρ, h'.symm⟩
    · exact absurd (h' ▸ h) ((Formalism.L2.Pj.cm_type_mem_iff_conj_not_mem D _).1 (hin ρ))
  have hinj : Function.Injective (tauE D) := fun _ _ h =>
    (GlobalTheory.CMTypePlaces.mk_tauE_bijective D).1 (by simp only [h])
  obtain ⟨hh, hd, hfg, hsp, -⟩ := GlobalTheory.Member.selfDualLat_neg_gram_transpose D V
  obtain ⟨n, hn, hnint⟩ := GlobalTheory.PrincData.exists_nat_herm_int (-(V.gram)ᵀ) (GlobalTheory.Member.latC V) hfg
  obtain ⟨k, hk, hkint⟩ := GlobalTheory.PrincData.exists_nat_int (-(2 * D.host.xi0))
  obtain ⟨X, hΨ, hG, hp, -, -, -, -, -, -⟩ := GlobalTheory.FlagData.exists_data GlobalTheory.latMinkowski D.host.E V.rank Q 3
    (3 * n * k) (Formalism.L2.Pj.cmTypeOfSqrt D) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V) D.host.xi0 (-(2 * D.host.xi0))
    (Formalism.L2.Pj.cm_type_mem_iff_conj_not_mem D) hh hd (by omega)
    (fun τ hτ => by
      obtain ⟨ρ, rfl⟩ := (hmem τ).1 hτ
      exact ⟨x ρ, hdet ρ, hgr ρ⟩)
    hfg hsp le_rfl (Formalism.L2.Pj.conj_xi0_alt D)
    (by
      obtain ⟨ρ, -⟩ := (GlobalTheory.CMTypePlaces.mk_tauE_bijective D).2 (InfinitePlace.mk D.host.φ₀)
      intro h
      have h1 := Formalism.L2.Theta.xi_zero_im_pos D ρ
      rw [h] at h1
      simp at h1)
    (Or.inr rfl)
    (fun τ hτ => by
      obtain ⟨ρ, rfl⟩ := (hmem τ).1 hτ
      have h1 := Formalism.L2.Theta.xi_zero_im_pos D ρ
      simp [map_ofNat]
      linarith)
    (by positivity)
    (fun u hu v hv => by
      have e1 : ((3 * n * k : ℕ) : D.host.E) / ((3 : ℕ) : D.host.E) * (-(2 * D.host.xi0)) *
          ReciprocityTheory.ChartRestriction.G.FD.herm (-(V.gram)ᵀ) u v =
          ((k : D.host.E) * (-(2 * D.host.xi0))) * ((n : D.host.E) * ReciprocityTheory.ChartRestriction.G.FD.herm (-(V.gram)ᵀ) u v) := by
        push_cast
        field_simp
      rw [e1]
      exact hkint.mul (hnint u hu v hv))
  let σ : D.what₂.Tau ≃ X.Ψ := Equiv.ofBijective (fun ρ => ⟨tauE D ρ, by rw [hΨ]; exact hin ρ⟩)
    ⟨fun _ _ h => hinj (congrArg Subtype.val h), fun τ => by
      obtain ⟨ρ, h⟩ := (hmem τ.1).1 (hΨ ▸ τ.2)
      exact ⟨ρ, Subtype.ext h.symm⟩⟩
  refine ⟨X, σ, fun τ => x (σ.symm τ), e, hG, fun ρ => rfl, fun τ => ?_, fun ρ => ⟨?_, ?_⟩⟩
  · have hτ : τ.1 = tauE D (σ.symm τ) := (congrArg Subtype.val (σ.apply_symm_apply τ)).symm
    show ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (x (σ.symm τ)) = _
    rw [hG, hp, hτ]
    exact hgr _
  · rw [hA ρ, hG]
    show gramAt D V ρ = -((-(V.gram)ᵀ).map (tauE D ρ))ᵀ
    rw [hmapT, neg_neg]
  · show A ρ * x (σ.symm (σ ρ)) = permM (e ρ)
    rw [σ.symm_apply_apply]
    exact hAx ρ

end GlobalTheory.CovTop.VolUp
end
end

section

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.FlagMod GlobalTheory.FlagPlucker

theorem _root_.GlobalTheory.T.pluckerMinors_sections_inverseDetFlagBundle : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) (Mc : MChart Y) {T : Scheme.{0}} (g : T ⟶ Z) (hg : ⊤ ≤ (g ≫ π) ⁻¹ᵁ Mc.U) (σ : E →+* ℂ) (m : Fin (Dw.mult σ)) (q : Fin (plkNum Mc m + 1)), ∃ s : ((F.LL (ind σ m)).pull g).Sec, s.f = plkLoc F Mc g hg σ m q := by
  first | exact @GlobalTheory.FlagPlucker.plkLoc_sec | exact GlobalTheory.FlagPlucker.plkLoc_sec | (intros; apply GlobalTheory.FlagPlucker.plkLoc_sec <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.DepthUnf GlobalTheory.SumSize GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.flatProductDepthPeriodic_gcd : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (e : AE D) (k k' : ℕ), DepthOK S t Φ β e k → DepthOK S t Φ β e k' → DepthOK S t Φ β e (Nat.gcd k k') := by
  first | exact @GlobalTheory.DepthUnf.depthOK_gcd | exact GlobalTheory.DepthUnf.depthOK_gcd | (intros; apply GlobalTheory.DepthUnf.depthOK_gcd <;> assumption)
end
