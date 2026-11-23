module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle315
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle316
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle286
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle319
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle313
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle314
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle112

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop GlobalTheory.TopStep
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.last_step_local_factor_target_law_top_level : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
  {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {G : ChGlob X R.m} {m2 : ℕ}, X.Ok → Pr.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs →
  ∀ (g : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))) (z : X.K), TopLev Ch sel mu cst (m2 + 1 + 1) P g z →
  ∃ Gg : GLint X.E (R.N (m2 + 1 + 1)) P.1, Gg.1 = g ∧ ∀ (k : GLint X.E (R.N (m2 + 1 + 1)) P.1), redGL _ P.1 k = redGL _ P.1 Gg →
  ∀ (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y' : Sp X.E (R.N (m2 + 1))),
    (∀ i, IntAt P.1 ((qOf P.1 : X.E) * y' i)) →
    z * (PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ ((k⁻¹).1.toLinearMap ∘ₗ y) ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst P (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ ((k⁻¹).1.toLinearMap ∘ₗ y)) y') * rhoT Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) =
      (PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst P (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y) y') := by
  first | exact @GlobalTheory.TwTop.topF_target_vG | exact GlobalTheory.TwTop.topF_target_vG | (intros; apply GlobalTheory.TwTop.topF_target_vG <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop GlobalTheory.TopStep
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.last_step_local_factor_source_law_coupled_level : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
  {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {G : ChGlob X R.m} {m2 : ℕ}, X.Ok → Pr.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (b : L.β (m2 + 1)) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs →
  ∀ (g : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1))) (z : X.K), MidLev Ch sel mu cst (m2 + 1) P (L.h (m2 + 1) b P) g z →
  ∃ Gg : GLint X.E (R.N (m2 + 1)) P.1, Gg.1 = g ∧ ∀ (k : GLint X.E (R.N (m2 + 1)) P.1), redGL _ P.1 k = redGL _ P.1 Gg →
  ∀ (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y' y'' : Sp X.E (R.N (m2 + 1))),
    (∀ i, IntAt P.1 ((qOf P.1 : X.E) * y' i)) → k.1 y'' - y' ∈ stdAt X.E _ P.1 →
    (PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ (y ∘ₗ k.1.toLinearMap) ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst P (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ (y ∘ₗ k.1.toLinearMap)) y'') * rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) =
      z * (PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst P (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y) y') := by
  first | exact @GlobalTheory.TopLawG.locTopG_source | exact GlobalTheory.TopLawG.locTopG_source | (intros; apply GlobalTheory.TopLawG.locTopG_source <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct

open Formalism.MainNotions.G.KAat Matrix

namespace GlobalTheory.CompanLocal

theorem mem_latS_dual_of_mem_latCo : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}
    (sp : Spaces R F E) (J : Matrix (Fin N) (Fin N) E) (crd : GL (Fin N) E) (a : 𝓞 E)
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), x ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F) → IsUnit J.det →
    ∀ (Lb : Submodule (𝓞 E) (Fin N → E)), Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ →
    (∀ y ∈ Lb, y ∈ dualSet (sp.cm.sig : E →+* E) J Lb) →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (u : Fin N → E), u ∈ latCo sp J crd a x Lb →
    ∃ z : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J Lb)),
      z.1 = fun l => prV (E := E) v (pullV (F := F) (ratA F crd * x) u l) := by
  intro R F E _ _ _ _ _ _ N sp J crd a x hx hJ Lb hfin hspan hint v u hu
  set y := bc (prV (E := E) v) x with hy_def
  simp only [latCo, mvL, Submodule.mem_map] at hu
  obtain ⟨w, hw, rfl⟩ := hu
  let locV : (Fin N → E) → (Fin N → E ⊗[F] v.adicCompletion F) := fun z i => inclE (F := F) (v.adicCompletion F) (z i)
  have hcomp : (fun l => prV (E := E) v (pullV (F := F) (ratA F crd * x)
      (((toLE crd : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)).restrictScalars (𝓞 E) w) l)) =
      ((y⁻¹ : GL (Fin N) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin N) (Fin N) (E ⊗[F] v.adicCompletion F)) *ᵥ locV w := by
    have h1 : pullV (F := F) (ratA F crd * x)
        (((toLE crd : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)).restrictScalars (𝓞 E) w) =
        ((x⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) _) *ᵥ
          (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (w i)) := by
      unfold pullV
      rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, ← map_inv]
      congr 1
      have := bc_mulVec (F := F) crd⁻¹ (toLE crd w)
      refine this.trans ?_
      funext i
      show inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (toLE crd⁻¹ (toLE crd w) i) = _
      rw [toLE_inv_apply']
    rw [h1, GlobalTheory.LocCarry.prV_mulVec, ← GlobalTheory.LocCarry.coe_bc_inv]
    congr 1
  have hlat : latAd x Lb = Formalism.UG.CS.globLat x Lb := Submodule.span_eq (Formalism.UG.CS.globLat x Lb)
  have hL : Submodule.IsFullLattice E (latAd x Lb) := by
    rw [hlat]; exact Formalism.UG.P.csGlob_lattice Lb hfin hspan x
  have hLb : Submodule.IsFullLattice E Lb := {
    toIsLattice := Submodule.IsLattice.of_fg E (Module.Finite.iff_fg.mp hfin)
    span_eq_top := hspan }
  have hyU : y ∈ UPts sp.cm.sig J (v.adicCompletion F) := Formalism.UG.P.afsplit_bc_mem _ J v x hx
  have hyl := fun z => GlobalTheory.LocCarry.mem_latS_latAd_iff x Lb hfin hspan v z
  have hdm := GlobalTheory.DualCompletion.dual_move F E sp.cm.sig N J v (latAd x Lb) Lb y hJ hL hLb hyU hyl
  have hsub : latS (F := F) (v.adicCompletion F) (intV E v) Lb ≤
      latS (F := F) (v.adicCompletion F) (intV E v) (Formalism.L2.Forms.dualL (sp.cm.sig : E →+* E) J Lb) :=
    Submodule.span_mono (Set.image_mono (fun z hz => Submodule.subset_span (hint z hz)))
  have hmem : ∀ (Λ : Submodule (𝓞 E) (Fin N → E)) z, z ∈ Λ → locV z ∈ latS (F := F) (v.adicCompletion F) (intV E v) Λ :=
    fun Λ z hz => Submodule.subset_span ⟨z, hz, rfl⟩
  simp only [compan] at hw
  obtain ⟨w1, hw1, w2, hw2, rfl⟩ := Submodule.mem_sup.1 hw
  have hw2' : w2 ∈ Formalism.L2.Forms.dualL (sp.cm.sig : E →+* E) J (latAd x Lb) := Submodule.smul_le_right hw2
  have hadd : locV (w1 + w2) = locV w1 + locV w2 := by funext i; simp [locV, map_add (f := _)]
  have key : ((y⁻¹ : GL (Fin N) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin N) (Fin N) (E ⊗[F] v.adicCompletion F)) *ᵥ
      locV (w1 + w2) ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Formalism.L2.Forms.dualL (sp.cm.sig : E →+* E) J Lb) := by
    rw [hadd, Matrix.mulVec_add]
    exact add_mem (hsub ((hyl _).1 (hmem _ _ hw1))) ((hdm _).1 (hmem _ _ hw2'))
  exact ⟨⟨_, key⟩, hcomp.symm⟩

end GlobalTheory.CompanLocal
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col GlobalTheory.TwU Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.MemDual

theorem prV_inclE {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    prV (E := E) v (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) e) = inclE (F := F) (v.adicCompletion F) e := by
  simp [prV, inclE]

theorem prV_sigR {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    prV (E := E) v (sigR σ (FiniteAdeleRing (𝓞 F) F) x) = sigR σ (v.adicCompletion F) (prV (E := E) v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]
  | tmul a b => simp [prV, sigR]

theorem bc_prV_mem_UPts {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    {k : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hk : k ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    bc (prV (E := E) v) k ∈ UPts σ J (v.adicCompletion F) := by
  have hg' : cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (k : Matrix (Fin n) (Fin n) _) *
      J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) * (k : Matrix (Fin n) (Fin n) _) =
      J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) := hk
  change cT (sigR σ (v.adicCompletion F)) ((k : Matrix (Fin n) (Fin n) _).map (prV (E := E) v)) *
      J.map (inclE (F := F) (v.adicCompletion F)) * ((k : Matrix (Fin n) (Fin n) _).map (prV (E := E) v)) =
      J.map (inclE (F := F) (v.adicCompletion F))
  have h1 : cT (sigR σ (v.adicCompletion F)) ((k : Matrix (Fin n) (Fin n) _).map (prV (E := E) v)) =
      (cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (k : Matrix (Fin n) (Fin n) _)).map (prV (E := E) v) := by
    ext i j
    simp [cT, prV_sigR]
  have hJ' : (J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))).map (prV (E := E) v) =
      J.map (inclE (F := F) (v.adicCompletion F)) := by
    ext i j
    simp [prV_inclE]
  rw [h1, ← hJ', ← Matrix.map_mul, ← Matrix.map_mul, hg']

theorem pullV_ratA_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (c : GL (Fin N) E) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (y : Fin N → E) :
    pullV (F := F) (ratA F c * x) ((c : Matrix (Fin N) (Fin N) E) *ᵥ y) =
      ((x⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) *ᵥ fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (y i) := by
  unfold pullV
  rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
  congr 1
  have hc : (((ratA F c)⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) =
      ((c⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) := by
    rw [← map_inv]; rfl
  rw [hc]
  ext i
  have := RingHom.map_mulVec (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))
    ((c⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) ((c : Matrix (Fin N) (Fin N) E) *ᵥ y) i
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
  rw [this]; rfl

end GlobalTheory.MemDual

namespace GlobalTheory.MemDual

theorem mem_latS_dual_of_latCo : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E), IsUnit J.det → ∀ (c : GL (Fin N) E) (a : 𝓞 E)
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), x ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F) →
    ∀ (Lb : Submodule (𝓞 E) (Fin N → E)), Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ →
    (∀ y ∈ Lb, y ∈ dualSet (sp.cm.sig : E →+* E) J Lb) → ∀ (v : HeightOneSpectrum (𝓞 F)) (y : Fin N → E),
    y ∈ latCo sp J c a x Lb →
    (fun l => prV (E := E) v (pullV (F := F) (ratA F c * x) y l)) ∈
      latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J Lb)) := by
  intro R F E _ _ _ _ _ _ sp N J hJ c a x hx Lb hfin hspan hdual v y hy
  obtain ⟨y', hy', rfl⟩ := hy
  set σ : E →ₐ[F] E := sp.cm.sig with hσ
  set Λ := latAd x Lb with hΛ
  set xv := bc (prV (E := E) v) x with hxv
  have hLb : Submodule.IsFullLattice E Lb := {
    toIsLattice := Submodule.IsLattice.of_fg E (Module.Finite.iff_fg.mp hfin)
    span_eq_top := hspan }
  have hLam : Submodule.IsFullLattice E Λ := by
    have hlat : Formalism.L2.PairingIndexBounds.F.latAd x Lb = Formalism.UG.CS.globLat x Lb := Submodule.span_eq (Formalism.UG.CS.globLat x Lb)
    rw [hΛ, hlat]
    exact Formalism.UG.P.csGlob_lattice Lb hfin hspan x
  have hxU : xv ∈ UPts σ J (v.adicCompletion F) := bc_prV_mem_UPts σ J v hx
  have hcarry := GlobalTheory.LocCarry.mem_latS_latAd_iff x Lb hfin hspan v

  have hpull : (fun l => prV (E := E) v (pullV (F := F) (ratA F c * x) ((c : Matrix (Fin N) (Fin N) E) *ᵥ y') l)) =
      ((xv⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) *ᵥ fun i => inclE (F := F) (v.adicCompletion F) (y' i) := by
    rw [pullV_ratA_mul, GlobalTheory.LocCarry.prV_mulVec, hxv, GlobalTheory.LocCarry.coe_bc_inv]
    congr 1
  show (fun l => prV (E := E) v (pullV (F := F) (ratA F c * x) ((c : Matrix (Fin N) (Fin N) E) *ᵥ y') l)) ∈ _
  rw [hpull]

  have hsub : compan (sp := sp) J a Λ ≤ Λ ⊔ dualL (σ : E →+* E) J Λ :=
    sup_le_sup_left (Submodule.smul_le_right) _
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp (hsub hy')
  have hadd : (fun i => inclE (F := F) (v.adicCompletion F) ((p + q) i)) =
      (fun i => inclE (F := F) (v.adicCompletion F) (p i)) + fun i => inclE (F := F) (v.adicCompletion F) (q i) := by
    ext i; simp
  rw [hadd, Matrix.mulVec_add]
  have hmono : latS (F := F) (v.adicCompletion F) (intV E v) Lb ≤
      latS (F := F) (v.adicCompletion F) (intV E v) (dualL (σ : E →+* E) J Lb) :=
    Submodule.span_mono (Set.image_mono fun z hz => Submodule.subset_span (hdual z hz))
  refine add_mem ?_ ?_
  · exact hmono ((hcarry _).1 (Submodule.subset_span ⟨p, hp, rfl⟩))
  · exact (GlobalTheory.DualCompletion.dual_move F E σ N J v Λ Lb xv hJ hLam hLb hxU hcarry _).1
      (Submodule.subset_span ⟨q, hq, rfl⟩)

end GlobalTheory.MemDual
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.complexCoordinates_columnFieldIdentification : ∀ {D : D7} {X : Fields} (s : Seam D X), s.Ok → ∀ (δ : ℂ) {a b : ℕ}, Function.Bijective (seamHom s (a := a) (b := b)) ∧ (∀ x : HomE D.host.E a b, embH (X.embC s.σ₀) δ (seamHom s x) = fun τ => embH (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ x (s.iT τ)) ∧ (∀ (M : Submodule (𝓞 X.E) (HomE X.E a b)) (M' : Submodule (𝓞 D.host.E) (HomE D.host.E a b)), (∀ x, seamHom s x ∈ M ↔ x ∈ M') → ∀ v : VV D.what₂.Tau a b, (fun τ => v (s.iT τ)) ∈ laV (X.embC s.σ₀) δ M ↔ v ∈ laV (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ M') ∧ (δ ≠ 0 → ∀ (Ξ : HomE X.E a b → ℂ) (v : VV D.what₂.Tau a b), onV (X.embC s.σ₀) δ Ξ (fun τ => v (s.iT τ)) = onV (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ (fun x => Ξ (seamHom s x)) v) := by
  first | exact @GlobalTheory.TwU.SeamEmb.seam_coords | exact GlobalTheory.TwU.SeamEmb.seam_coords | (intros; apply GlobalTheory.TwU.SeamEmb.seam_coords <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_vector_prescribed_cosets_badPrimes_frames : ∀ {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) {n : ℕ} (f : rowSG Pr sel mu → (Sp X.E n ≃ₗ[X.E] Sp X.E n)) (y0 : rowSG Pr sel mu → Sp X.E n),
  ∃ y : Sp X.E n, ∀ P, SameCoset sel mu cst P ((f P).symm y) (y0 P) := by
  first | exact @GlobalTheory.CosetApprox.exists_sameCoset | exact GlobalTheory.CosetApprox.exists_sameCoset | (intros; apply GlobalTheory.CosetApprox.exists_sameCoset <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_vector_sameCouplingCoset_all_bad_primes : ∀ {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {n : ℕ} (fr : rowSG Pr sel mu → (Sp X.E n ≃ₗ[X.E] Sp X.E n)) (y0 : rowSG Pr sel mu → Sp X.E n), ∃ y : Sp X.E n, ∀ P, SameCoset sel mu cst P ((fr P).symm y) (y0 P) := by
  exact @GlobalTheory.FrameCongApprox.exists_sameCoset
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

theorem _root_.GlobalTheory.T.levelPrimeFunctionals_move_rational_lattice_aut : ∀ {D : D7} {X : Fields} (s : Seam D X) {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (lev : Formalism.L2.Forms.StepLevel D.host.F D.host.E (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D i hi) T D.R.f bad) {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (P : ST) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (T : 𝓞 D.host.F) ∈ v.asIdeal) (ι : lev.fM v h →+ 𝓞 X.E ⧸ P.1.asIdeal) (x : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (d : Deco X.E (D.R.N i) ST SG) (g : Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)) (hh : GLG (E := X.E) (n := D.R.N i) (SG := SG)), FunMoved s lev P v h ι x d → FunMoved s lev P v h ι (ratA D.host.F (seamGL s g) * x) (d.act g hh) := by
  first | exact @GlobalTheory.TwU.funMoved_ratA_act | exact GlobalTheory.TwU.funMoved_ratA_act | (intros; apply GlobalTheory.TwU.funMoved_ratA_act <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.primeSetExponent_transport_fieldIsomorphism : ∀ {D : D7} {X : Fields} (s : Seam D X), s.Ok → ∀ (SS : Finset (HeightOneSpectrum (𝓞 X.E))) (P : HeightOneSpectrum (𝓞 X.E)), expS (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) (seamP s P) = expS SS P := by
  first | exact @GlobalTheory.TwU.SeamExp.expS_seam | exact GlobalTheory.TwU.SeamExp.expS_seam | (intros; apply GlobalTheory.TwU.SeamExp.expS_seam <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

theorem _root_.GlobalTheory.T.transportedLattice_of_linearAutImage_eq_matrixImage : ∀ {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (g : Sp X.E n ≃ₗ[X.E] Sp X.E n) (N : Submodule (𝓞 X.E) (Sp X.E n)), s.lat (Formalism.HermitianLatticesTheory.gmap g N) = Formalism.MainNotions.G.KAat.mvL (seamGL s g) (s.lat N) := by
  first | exact @GlobalTheory.RatLat.lat_gmap | exact GlobalTheory.RatLat.lat_gmap | (intros; apply GlobalTheory.RatLat.lat_gmap <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.topRankLevel_mem_integralGL_at_twist_prime : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (j : ℕ) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
  ∀ (g : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)) (z : X.K), TopLev Ch sel mu cst j P g z → g ∈ GLint X.E (R.N j) P.1 := by
  first | exact @GlobalTheory.TopLevInt.mem_GLint_of_topLev | exact GlobalTheory.TopLevInt.mem_GLint_of_topLev | (intros; apply GlobalTheory.TopLevInt.mem_GLint_of_topLev <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

theorem _root_.GlobalTheory.T.adelicPointLattice_mul_rationalGL : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ} (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (g : GL (Fin N) E) (M : Submodule (𝓞 E) (Fin N → E)), latAd (y * ratA F g) M = latAd y (mvL g M) := by
  first | exact @GlobalTheory.TwV.latAd_mul_ratA | exact GlobalTheory.TwV.latAd_mul_ratA | (intros; apply GlobalTheory.TwV.latAd_mul_ratA <;> assumption)
end
