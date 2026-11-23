module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle151
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle080
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.whittaker_functional_torus_valuation_bound : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V), IsSmooth ρ → ∀ l : Module.Dual ℂ V, IsFunctional ψ ρ l → ∀ x : V, ∃ r : kˣ, ∀ (t : Fin n → kˣ) (i j : Fin n), j.val = i.val + 1 → l (ρ (diagT k (Fin n) t) x) ≠ 0 → valuation k ((t i : k) / t j) ≤ valuation k (r : k) := by
  first | exact @GlobalTheory.RootUp.whittaker_torus_root_bound | exact GlobalTheory.RootUp.whittaker_torus_root_bound | (intros; apply GlobalTheory.RootUp.whittaker_torus_root_bound <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.whittaker_torus_twKer_rootBound' : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V) (l : Module.Dual ℂ V), IsFunctional ψ ρ l → ∀ (a b : ℕ) (h : ∑ i, ![a, b] i = n) (i j : Fin n), i.val + 1 = a → j.val = a → ∀ x ∈ twKer ρ (unipRad k (stdBlocks ![a, b] h)) 1, ∃ r : kˣ, ∀ t : Fin n → kˣ, l (ρ (diagT k (Fin n) t) x) ≠ 0 → valuation k (r : k) ≤ valuation k ((t i : k) / t j) := by
  first | exact @GlobalTheory.whittaker_torus_twKer_rootBound | exact GlobalTheory.whittaker_torus_twKer_rootBound | (intros; apply GlobalTheory.whittaker_torus_twKer_rootBound <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.VolSplit

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {r : ℕ}

theorem map_sigR {A B : Type} [CommRing A] [Algebra F A] [CommRing B] [Algebra F B] (p : A →ₐ[F] B) (z : A ⊗[F] E) :
    (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom (sigR A σ z) =
      sigR B σ ((Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem map_JR {A B : Type} [CommRing A] [Algebra F A] [CommRing B] [Algebra F B] (p : A →ₐ[F] B)
    (J : Matrix (Fin r) (Fin r) E) :
    (JR A J).map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom = JR B J := by
  ext i j; simp [JR, inclR]

theorem map_unit {A B : Type} [CommRing A] [Algebra F A] [CommRing B] [Algebra F B] (p : A →ₐ[F] B)
    (J : Matrix (Fin r) (Fin r) E) (g : Matrix (Fin r) (Fin r) (A ⊗[F] E)) :
    (Formalism.UG.cT (sigR A σ) g * JR A J * g).map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom =
      Formalism.UG.cT (sigR B σ) (g.map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom) * JR B J *
        g.map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom := by
  rw [Matrix.map_mul, Matrix.map_mul, map_JR]
  congr 2
  ext i j
  exact map_sigR σ p _

end Gen

theorem exists_adelic_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), ∃ e : HA (AF F) σ J ≃ₜ* HA (Ainf F) σ J × HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J, ∀ h, ((HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J (e h).2 : GL (Fin M) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)) = finMat σ J h ∧ ((HA.mat (Ainf F) σ J (e h).1 : GL (Fin M) (Ainf F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Ainf F ⊗[F] E)) = ((HA.mat (AF F) σ J h : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) := by
  intro F E _ _ _ _ _ σ r J
  let pInf : AF F ⊗[F] E →+* Ainf F ⊗[F] E := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
  let pFin : AF F ⊗[F] E →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
  obtain ⟨e, he, hc, hc'⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  have ext : ∀ {M N : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)}, M.map pInf = N.map pInf → M.map pFin = N.map pFin →
      M = N := fun {M N} h1 h2 => by
    ext i j
    refine e.injective (Prod.ext ?_ ?_)
    · rw [(he _).1, (he _).1]; exact congrFun (congrFun h1 i) j
    · rw [(he _).2, (he _).2]; exact congrFun (congrFun h2 i) j
  let gl : Matrix (Fin r) (Fin r) (Ainf F ⊗[F] E) → Matrix (Fin r) (Fin r) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) →
      Matrix (Fin r) (Fin r) (AF F ⊗[F] E) := fun M N => Matrix.of fun i j => e.symm (M i j, N i j)
  have g1 : ∀ M N, (gl M N).map pInf = M := fun M N => by
    ext i j
    exact ((he _).1.symm.trans (congrArg Prod.fst (e.apply_symm_apply _)))
  have g2 : ∀ M N, (gl M N).map pFin = N := fun M N => by
    ext i j
    exact ((he _).2.symm.trans (congrArg Prod.snd (e.apply_symm_apply _)))
  let χ : HA (AF F) σ J →* HA (Ainf F) σ J × HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J :=
    { toFun := fun h => ((⟨Formalism.UG.bc pInf (HA.mat _ _ _ h), (by
          have := congrArg (fun M => M.map pInf) (show Formalism.UG.cT _ _ * _ * _ = _ from h.2)
          rw [map_unit σ (fstA F), map_JR (fstA F)] at this
          exact this)⟩ : HR (Ainf F) σ J),
        (⟨Formalism.UG.bc pFin (HA.mat _ _ _ h), (by
          have := congrArg (fun M => M.map pFin) (show Formalism.UG.cT _ _ * _ * _ = _ from h.2)
          rw [map_unit σ (sndA F), map_JR (sndA F)] at this
          exact this)⟩ : HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J))
      map_one' := Prod.ext (Subtype.ext (map_one (Formalism.UG.bc pInf))) (Subtype.ext (map_one (Formalism.UG.bc pFin)))
      map_mul' := fun a b => Prod.ext (Subtype.ext (map_mul (Formalism.UG.bc pInf) _ _))
        (Subtype.ext (map_mul (Formalism.UG.bc pFin) _ _)) }
  let ω : HA (Ainf F) σ J × HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J → HA (AF F) σ J := fun g =>
    (⟨⟨gl g.1.1.val g.2.1.val, gl g.1.1.inv g.2.1.inv,
      ext (by rw [Matrix.map_mul, g1, g1, g.1.1.val_inv]; simp) (by rw [Matrix.map_mul, g2, g2, g.2.1.val_inv]; simp),
      ext (by rw [Matrix.map_mul, g1, g1, g.1.1.inv_val]; simp) (by rw [Matrix.map_mul, g2, g2, g.2.1.inv_val]; simp)⟩,
      ext ((map_unit σ (fstA F) J _).trans (Eq.trans (by
        rw [g1]
        exact g.1.2) (map_JR (fstA F) J).symm)) ((map_unit σ (sndA F) J _).trans (Eq.trans (by
        rw [g2]
        exact g.2.2) (map_JR (sndA F) J).symm))⟩ : HR (AF F) σ J)
  have l1 : Function.LeftInverse ω χ := fun h => Subtype.ext (Units.ext (ext (g1 _ _) (g2 _ _)))
  have l2 : Function.RightInverse ω χ := fun g =>
    Prod.ext (Subtype.ext (Units.ext (g1 _ _))) (Subtype.ext (Units.ext (g2 _ _)))
  let ψ : HA (AF F) σ J ≃* HA (Ainf F) σ J × HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J :=
    { χ with invFun := ω, left_inv := l1, right_inv := l2 }
  have hp1 : Continuous pInf := (continuous_fst.comp hc).congr fun z => (he z).1
  have hp2 : Continuous pFin := (continuous_snd.comp hc).congr fun z => (he z).2
  have hv : Continuous fun h : HA (AF F) σ J => HA.mat _ _ _ h := continuous_subtype_val
  have c1 : Continuous ψ := by
    refine Continuous.prodMk (Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _)
      (Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _)
    · exact (Units.continuous_val.comp hv).matrix_map hp1
    · exact (Units.continuous_coe_inv.comp hv).matrix_map hp1
    · exact (Units.continuous_val.comp hv).matrix_map hp2
    · exact (Units.continuous_coe_inv.comp hv).matrix_map hp2
  have c2 : Continuous ψ.symm := by
    refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
    · refine continuous_matrix fun i j => hc'.comp (Continuous.prodMk ?_ ?_)
      · exact (Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst)).matrix_elem i j
      · exact (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)).matrix_elem i j
    · refine continuous_matrix fun i j => hc'.comp (Continuous.prodMk ?_ ?_)
      · exact (Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_fst)).matrix_elem i j
      · exact (Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_snd)).matrix_elem i j
  exact ⟨{ ψ with continuous_toFun := c1, continuous_invFun := c2 }, fun h => ⟨rfl, rfl⟩⟩

end GlobalTheory.Mem.VolSplit
end
