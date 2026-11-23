module

import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle048
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle028
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle045
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraEigenDecompositionCMSignature
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsRigTransport
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.Bundle001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleQuadraticExistsUnitEqMulSg
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle321
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsTwistCharacterUnitsModSpecialIdeal
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle049
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.CMCurveHermitianForms
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle022
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle002
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle001

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.PointAtPlace

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice NumberField

variable {D : D7}

theorem tauE_injective : Function.Injective (tauE D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem tauE_cm (σ : D.host.E →+* ℂ) :
    (∃ ρ, tauE D ρ = σ) ↔ ¬ ∃ ρ, tauE D ρ = ComplexEmbedding.conjugate σ := by
  apply GlobalTheory.SmoothForms.RealPts.tauE_cm <;> assumption

theorem archM_mul (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (a b : GA D V) :
    Formalism.L2.Pj.archM V θ (a * b) = Formalism.L2.Pj.archM V θ a * Formalism.L2.Pj.archM V θ b := by
  unfold Formalism.L2.Pj.archM
  rw [map_mul, Units.val_mul, Matrix.map_mul]

theorem archM_one (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) :
    Formalism.L2.Pj.archM V θ 1 = 1 := by
  unfold Formalism.L2.Pj.archM
  rw [map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem eq_one_of_mem (V : HSp D) (k : GA D V) (h1 : k ∈ GfC V) (h2 : k ∈ GinfC V) : k = 1 := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have a1 : (infHom V k).1 = (infHom V 1).1 := by rw [map_one]; exact congrArg Units.val h1
  have a2 : (finHom V k).1 = (finHom V 1).1 := by rw [map_one]; exact congrArg Units.val h2
  refine Subtype.ext (Units.ext (Matrix.ext fun a b => e.injective (Prod.ext ?_ ?_)))
  · rw [(he _).1, (he _).1]; exact congrFun (congrFun a1 a) b
  · rw [(he _).2, (he _).2]; exact congrFun (congrFun a2 a) b

theorem existsUnique_isAtTau (V : HSp D) (τ : D.what₂.Tau)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.BasicNotions.TH.gramAt D V τ)) :
    ∃! h : GA D V, IsAtTau θ V τ g h := by
  classical
  let Ψ : Finset (D.host.E →+* ℂ) := Finset.univ.filter fun σ => ∃ ρ, tauE D ρ = σ
  have hmem : ∀ σ, σ ∈ Ψ ↔ ∃ ρ, tauE D ρ = σ := fun σ => by simp [Ψ]
  choose r hr using fun σ : Ψ => (hmem σ.1).1 σ.2
  have hsurj : ∀ ρ, r ⟨tauE D ρ, (hmem _).2 ⟨ρ, rfl⟩⟩ = ρ := fun ρ => tauE_injective (hr _)
  obtain ⟨h1, -, -, h2⟩ := (GlobalTheory.UnitaryGlue.adelic_glue D V).2 Ψ (fun σ => θ (r σ))
    (fun σ => by rw [hmem, hmem]; exact tauE_cm σ) (fun σ => by rw [← hr σ]; exact hθ _)
  obtain ⟨h, hh, hu⟩ := h2 (fun σ => if r σ = τ then g else 1) (fun σ => by
    by_cases c : r σ = τ
    · rw [if_pos c, ← hr σ, c]
      exact hg
    · rw [if_neg c, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul,
        Matrix.mul_one])
  have hu' : ∀ ρ, Formalism.L2.Pj.archM V (θ ρ) h = if ρ = τ then g else 1 := fun ρ => by
    have := hu ⟨tauE D ρ, (hmem _).2 ⟨ρ, rfl⟩⟩
    simp only [hsurj] at this
    exact this
  refine ⟨h, ⟨hh, (hu' τ).trans (if_pos rfl), fun ρ c => (hu' ρ).trans (if_neg c)⟩, fun h' hh' => ?_⟩
  have e : ∀ ρ, Formalism.L2.Pj.archM V (θ ρ) h' = Formalism.L2.Pj.archM V (θ ρ) h := fun ρ => by
    rw [hu']
    by_cases c : ρ = τ
    · rw [if_pos c, c]; exact hh'.2.1
    · rw [if_neg c]; exact hh'.2.2 ρ c
  refine mul_inv_eq_one.1 (eq_one_of_mem V _ (h1 _ fun σ => ?_) (mul_mem hh'.1 (inv_mem hh)))
  rw [archM_mul, e, ← archM_mul, mul_inv_cancel, archM_one]

end GlobalTheory.PointAtPlace
end
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory.CM GlobalTheory.IndefiniteRowSideFullHecke

noncomputable section
namespace GlobalTheory.CMSharedCompare

section Comb

variable {R : Type} [CommRing R]

end Comb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]

section Vec

variable {t : SAB H (Sp (𝓞 K))} (G : EigenLatticeFibres.GenFib t)

end Vec

structure Partner {T : PAT H (Sp (𝓞 K))} (F : GenFib T.pol) where

  tK : SAB H (Sp K)

  m : SABMap tK T.t (spMap (algebraMap (𝓞 K) K))

  v : Fin F.P₀.g → (epsR K ⟶ tK.G)
  basis : IsLieBasis v
  same : ∀ i, (v i).left ≫ m.φ = (F.v i).left ≫ F.φ

variable {T T' : PAT H (Sp (𝓞 K))}

namespace Partner

variable {F : GenFib T.pol} {F' : GenFib T'.pol} (Q : Partner F) (Q' : Partner F')

end Partner

section Metric

variable {T : PAT H (Sp (𝓞 K))} {F : GenFib T.pol} (Q : Partner F)

end Metric

section Embeddings

end Embeddings

section Isogeny

end Isogeny

section Object

theorem nonempty_genFib (P : Out.PolAV (Sp (𝓞 K))) : Nonempty (GenFib P) := by
  have := P.isAb.comm
  have h := isGrpPullback_pullback P.A (spMap (algebraMap (𝓞 K) K))
  obtain ⟨v, hv⟩ := TenDim.exists_isLieBasis _ (TorsionTauCompare.polOfPullback P _ h).smoothDim
  exact ⟨⟨TorsionTauCompare.polOfPullback P _ h, _, ⟨rfl, h, PolBaseChange.lbIso_refl (pull_isLB P.isLB _)⟩, v, hv⟩⟩

theorem dim_eq {ρ : 𝓞 K} {p q : ℕ} (T : PAT H (Sp (𝓞 K))) (hs : Splits E K) (ht : HasType H T.t.act ρ p q)
    (hρ : ρ ^ 2 = -(H.d : 𝓞 K)) : T.g = Module.finrank ℚ E / 2 * (p + q) := by
  obtain ⟨F⟩ := nonempty_genFib T.pol
  exact (EigDec.eigen_decomposition E H K ρ T F p q hs ht hρ).2.2.2.1

variable {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ}

end Object

end GlobalTheory.CMSharedCompare
end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdeleNinety

theorem fixed_baseChange {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (c : E →ₐ[F] E) (hcc : ∀ x, c (c x) = x)
    (hfix : ∀ x, c x = x → ∃ t : F, x = algebraMap F E t) (y : R ⊗[F] E)
    (hy : Algebra.TensorProduct.map (AlgHom.id F R) c y = y) : ∃ a : R, y = a ⊗ₜ 1 := by
  have hT : ∀ z : R ⊗[F] E, ∃ t : R, z + Algebra.TensorProduct.map (AlgHom.id F R) c z = t ⊗ₜ 1 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a x =>
      obtain ⟨t, ht⟩ := hfix (x + c x) (by rw [map_add (f := _), hcc, add_comm])
      refine ⟨t • a, ?_⟩
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, ← TensorProduct.tmul_add, ht,
        Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add x y hx hy =>
      obtain ⟨t, ht⟩ := hx
      obtain ⟨t', ht'⟩ := hy
      refine ⟨t + t', ?_⟩
      rw [map_add (f := _), TensorProduct.add_tmul, ← ht, ← ht']; ring
  obtain ⟨t, ht⟩ := hT y
  refine ⟨(2 : F)⁻¹ • t, ?_⟩
  rw [← TensorProduct.smul_tmul', ← ht, hy, ← two_smul F y, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

theorem conj_ne_one (D : D7) : cF D ≠ 1 := by
  intro h
  obtain ⟨P, hM⟩ := Ideal.exists_maximal (𝓞 D.host.E)
  obtain ⟨t, s, hs, hts⟩ := D.sp.cm.cmUnram.2.2 P hM
  have hs' : (s : D.host.E) = cF D (t : D.host.E) := hs
  rw [h] at hs'
  have : s = t := Subtype.ext hs'
  rw [this, sub_self] at hts
  exact hts P.zero_mem

theorem fixed_conj (D : D7) (x : D.host.E) (hx : cF D x = x) : ∃ t : D.host.F, x = algebraMap D.host.F D.host.E t := by
  have : Algebra.IsQuadraticExtension D.host.F D.host.E := { finrank_eq_two' := D.sp.cm.deg2 }
  have hcard : Nat.card (D.host.E ≃ₐ[D.host.F] D.host.E) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, D.sp.cm.deg2]
  obtain ⟨g, -, hg⟩ := (Nat.card_eq_two_iff' (1 : D.host.E ≃ₐ[D.host.F] D.host.E)).1 hcard
  obtain ⟨t, ht⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := D.host.F) x).2 fun f => by
    by_cases hf : f = 1
    · rw [hf]; rfl
    · rw [hg f hf, ← hg _ (conj_ne_one D), hx]
  exact ⟨t, ht.symm⟩

theorem coe_cjFin (D : D7) (y : (AfE D)ˣ) : ((cjFin D y : (AfE D)ˣ) : AfE D) = barF D (y : AfE D) := by
  have h : D.conjF = (cF D : D.host.E →ₐ[D.host.F] D.host.E) :=
    AlgHom.ext fun x => (D.conjF_eq x).trans (Formalism.BasicNotions.Examples₂.star_eq_conj D.host x).symm
  unfold cjFin barF
  rw [h]
  rfl

theorem finiteIdeles_normOne_eq_div_conj_with_congruence : ∀ (D : D7), (∀ x : (AfE D)ˣ, NormOne x → ∃ y, x = y / cjFin D y) ∧ (∀ y : (AfE D)ˣ, cjFin D y = y → ∃ a : Af D.host.F, (y : AfE D) = a ⊗ₜ 1) ∧ ∀ (p N : ℕ) (x : (AfE D)ˣ), p.Prime → p ≠ 2 → p ∣ N → 0 < N → NormOne x → CongOne N x → ∃ y, IntUnit y ∧ CongOne p y ∧ x = y / cjFin D y := by
  intro D
  have hcc : ∀ x, cF D (cF D x) = x := fun x => star_star x
  refine ⟨fun x hx => ?_, fun y hy => ?_, fun p N x hp h2 hpN _ hx hc => ?_⟩
  · obtain ⟨y, hy⟩ := GlobalTheory.UCls.NormOne.finiteAdele_quadratic_exists_unit_eq_mul_sg (cF D) hcc (fixed_conj D) (conj_ne_one D) (x : AfE D) hx
    refine ⟨y, ?_⟩
    rw [eq_div_iff_mul_eq']
    exact Units.ext (by rw [Units.val_mul, coe_cjFin]; exact hy.symm)
  · exact fixed_baseChange (Af D.host.F) (cF D : D.host.E →ₐ[D.host.F] D.host.E) hcc (fixed_conj D) _
      ((coe_cjFin D y).symm.trans (congrArg Units.val hy))
  · obtain ⟨w, hw, hwe⟩ := hc
    obtain ⟨k, rfl⟩ := hpN
    obtain ⟨y, y', hy, hy', hyy, hroot, hq⟩ := GlobalTheory.OddRoot.exists_root_odd D p (hp.odd_of_ne_two h2) (x : AfE D)
      (k • w) (nsmul_mem hw k) (by rw [hwe, mul_smul]) hx
    refine ⟨Units.mkOfMulEqOne y y' hyy, ⟨hy, hy'⟩, hq, ?_⟩
    rw [eq_div_iff_mul_eq']
    exact Units.ext (by rw [Units.val_mul, coe_cjFin]; exact hroot.symm)

end GlobalTheory.IdeleNinety
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin GlobalTheory.FinalJoin2

namespace GlobalTheory.FinalJoin2

theorem FO_eq_coeff {D : D7} (Q : Par D) (h : Q.PinField) : FO D = Q.c.F := by
  apply le_antisymm
  · rw [FO, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, rfl⟩
    have e := h (Q.eO.symm y)
    rw [RingEquiv.apply_symm_apply] at e
    have e' : D.what₂.phiO y = ((Q.eO.symm y : Q.c.F) : ℂ) := e
    rw [e']
    exact SetLike.coe_mem _
  · intro z hz
    haveI := Q.c.fin
    haveI : NumberField Q.c.F := NumberField.mk
    have hint : ∀ x : 𝓞 Q.c.F, ((algebraMap (𝓞 Q.c.F) Q.c.F x : Q.c.F) : ℂ) ∈ FO D := fun x => by
      have e : D.what₂.phiO (Q.eO x) = ((algebraMap (𝓞 Q.c.F) Q.c.F x : Q.c.F) : ℂ) := h x
      rw [← e]
      exact phiO_mem_FO D _
    obtain ⟨x, y, -, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 Q.c.F) (⟨z, hz⟩ : Q.c.F)
    have : z = ((algebraMap (𝓞 Q.c.F) Q.c.F x : Q.c.F) : ℂ) / ((algebraMap (𝓞 Q.c.F) Q.c.F y : Q.c.F) : ℂ) := by
      have := congrArg (fun t : Q.c.F => (t : ℂ)) hxy
      simpa using this.symm
    rw [this]
    exact div_mem (hint x) (hint y)

theorem fieldSmall_iff_opo : ∀ (D : D7) (T : Top D) (h : LawsP T) (large₂ : SizeData₂ D),
    FieldSmall D large₂ ↔ OPO large₂ (recB h.toLawsCore) := by
  intro D T h large₂
  have hF : FO D = T.Q.c.F := FO_eq_coeff T.Q h.toLawsCore.pins.2.2.1
  letI : NumberField (FO D) := NumberField.mk
  let e : FO D ≃+* (recB h.toLawsCore).KO := (IntermediateField.equivOfEq hF).toRingEquiv
  have h1 : Module.finrank ℚ (FO D) = Module.finrank ℚ (recB h.toLawsCore).KO :=
    (LinearEquiv.ofBijective e.toRingHom.toRatAlgHom.toLinearMap e.bijective).finrank_eq
  have h2 : NumberField.discr (FO D) = NumberField.discr (recB h.toLawsCore).KO :=
    NumberField.discr_eq_discr_of_ringEquiv _ e
  unfold FieldSmall OPO
  rw [← h1, ← h2]

end GlobalTheory.FinalJoin2
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_twistCharacter_units_mod_specialIdeal : ∀ (D : D7) (p : ℕ) (I : Ideal (𝓞 D.host.E)) (xi : (AfE D)ˣ →* ℂˣ), p.Prime → p.Coprime (D.host.g 0 * D.host.g 1) → I * I.map (barE D : 𝓞 D.host.E →+* 𝓞 D.host.E) = Ideal.span {((p : ℕ) : 𝓞 D.host.E)} → I ⊔ I.map (barE D : 𝓞 D.host.E →+* 𝓞 D.host.E) = ⊤ → XiOK D p xi → ∃ χ : (𝓞 D.host.E ⧸ I)ˣ →* (FO D)ˣ, χ ≠ 1 ∧ ∀ (x : (AfE D)ˣ) (a : 𝓞 D.host.E) (u : (𝓞 D.host.E ⧸ I)ˣ), NormOne x → CongOne (D.host.g 0 * D.host.g 1) x → (u : 𝓞 D.host.E ⧸ I) = Ideal.Quotient.mk I a → (x : AfE D) - 1 ⊗ₜ (a : D.host.E) ∈ GlobalTheory.AdLat.hat1 D.host.F ((algebraMap (𝓞 D.host.E) D.host.E) '' (I : Set (𝓞 D.host.E))) → ((xi x : ℂˣ) : ℂ) = (((χ u : (FO D)ˣ) : FO D) : ℂ) := by
  first | exact @GlobalTheory.TwistChar.exists_char_of_xiOK | exact GlobalTheory.TwistChar.exists_char_of_xiOK | (intros; apply GlobalTheory.TwistChar.exists_char_of_xiOK <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos


theorem _root_.GlobalTheory.T.coeffWord_moderateGrowth_bound : ∀ (n : ℕ) (ε : Fin n → Bool) (N : ℕ) (f : Mx n → ℂ) (F : List (Mx n) → Mx n → ℂ),
    (∀ g ∈ UJset ε, F [] g = f g) → IsDerFam ε F → FamGrowth ε N F →
    ∀ u : List (Ltr ε), ∃ C : ℝ, ∀ g ∈ UJset ε, ‖wordF u f g‖ ≤ C * (1 + Formalism.REAL.hs g) ^ N := by
  first | exact @GlobalTheory.TypeSum.CoefClos.wordF_growth | exact GlobalTheory.TypeSum.CoefClos.wordF_growth | (intros; apply GlobalTheory.TypeSum.CoefClos.wordF_growth <;> assumption)
end

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined

noncomputable section

namespace GlobalTheory.TypeSum.CasBasis.PB

variable {n : ℕ}

theorem tr_unit (a b c d : Fin n) :
    trace (unitE a b * unitE c d) = if b = c ∧ d = a then 1 else 0 := by
  by_cases hbc : b = c
  · subst hbc
    rw [unitE, unitE, Matrix.single_mul_single_same, one_mul]
    by_cases hda : d = a
    · subst hda; simp [Matrix.trace_single_eq_same]
    · rw [Matrix.trace_single_eq_of_ne (h := Ne.symm hda)]; simp [hda]
  · rw [unitE, unitE, Matrix.single_mul_single_of_ne _ _ _ _ hbc]; simp [hbc]

theorem sq_inv : invSqrtTwo * invSqrtTwo = (1 / 2 : ℂ) := by
  rw [invSqrtTwo, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  push_cast; ring

def B (X Y : Mx n) : ℝ := (trace (X * Y)).re

theorem B_comm (X Y : Mx n) : B X Y = B Y X := by
  simp only [B, Matrix.trace_mul_comm X Y]

def f (p : Fin n × Fin n) : List (Mx n) :=
  [invSqrtTwo • (unitE p.1 p.2 + unitE p.2 p.1), (invSqrtTwo * Complex.I) • (unitE p.1 p.2 - unitE p.2 p.1)]

theorem pList_eq (ε : Fin n → Bool) : pList ε = (pairs ε false).flatMap f := rfl

theorem mem_pairs' {ε : Fin n → Bool} {p : Fin n × Fin n} (h : p ∈ pairs ε false) : p.1 < p.2 := by
  simp only [pairs, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2.1

theorem nodup_pairs (ε : Fin n → Bool) : (pairs ε false).Nodup :=
  (List.Nodup.product (List.nodup_finRange n) (List.nodup_finRange n)).filter _

theorem norm_one {a b : Fin n} (hab : a < b) : ∀ X ∈ f (a, b), B X X = 1 := by
  have h1 : a ≠ b := hab.ne
  have h2 : b ≠ a := hab.ne'
  intro X hX
  simp only [f, List.mem_cons, List.not_mem_nil, or_false] at hX
  rcases hX with rfl | rfl
  · simp only [B, smul_mul_smul_comm, Matrix.trace_smul, mul_add, add_mul, Matrix.trace_add, tr_unit,
      h1, h2, and_self, and_false, false_and, if_true, if_false, sq_inv, smul_eq_mul]
    norm_num
  · simp only [B, smul_mul_smul_comm, Matrix.trace_smul, mul_sub, sub_mul, Matrix.trace_sub, tr_unit,
      h1, h2, and_self, and_false, false_and, if_true, if_false, smul_eq_mul]
    have : invSqrtTwo * Complex.I * (invSqrtTwo * Complex.I) = -(1 / 2 : ℂ) := by
      rw [show invSqrtTwo * Complex.I * (invSqrtTwo * Complex.I) = invSqrtTwo * invSqrtTwo * (Complex.I * Complex.I) by ring,
        sq_inv, Complex.I_mul_I]; ring
    rw [this]; norm_num

theorem within {a b : Fin n} (hab : a < b) : (f (a, b)).Pairwise fun X Y => B X Y = 0 := by
  have h1 : a ≠ b := hab.ne
  have h2 : b ≠ a := hab.ne'
  simp only [f, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
    List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true]
  simp only [B, smul_mul_smul_comm, Matrix.trace_smul, mul_sub, add_mul, Matrix.trace_sub, Matrix.trace_add, tr_unit,
    h1, h2, and_self, and_false, false_and, if_true, if_false, smul_eq_mul]
  simp

theorem across {a b c d : Fin n} (hab : a < b) (hcd : c < d) (hne : (a, b) ≠ (c, d)) :
    ∀ X ∈ f (a, b), ∀ Y ∈ f (c, d), B X Y = 0 := by
  have e1 : ¬ (b = c ∧ d = a) := by rintro ⟨rfl, rfl⟩; exact lt_asymm hab hcd
  have e2 : ¬ (b = d ∧ c = a) := by rintro ⟨rfl, rfl⟩; exact hne rfl
  have e3 : ¬ (a = c ∧ d = b) := by rintro ⟨rfl, rfl⟩; exact hne rfl
  have e4 : ¬ (a = d ∧ c = b) := by rintro ⟨rfl, rfl⟩; exact lt_asymm hab hcd
  intro X hX Y hY
  simp only [f, List.mem_cons, List.not_mem_nil, or_false] at hX hY
  rcases hX with rfl | rfl <;> rcases hY with rfl | rfl <;>
  simp only [B, smul_mul_smul_comm, Matrix.trace_smul, mul_sub, sub_mul, mul_add, add_mul, Matrix.trace_sub,
    Matrix.trace_add, tr_unit, e1, e2, e3, e4, if_false, sub_zero, add_zero, smul_zero, Complex.zero_re]

theorem pairwise_pList (ε : Fin n → Bool) : (pList ε).Pairwise fun X Y => B X Y = 0 := by
  rw [pList_eq, List.pairwise_flatMap]
  refine ⟨fun p hp => ?_, ?_⟩
  · obtain ⟨a, b⟩ := p
    exact within (mem_pairs' hp)
  · refine (nodup_pairs ε).imp_of_mem fun {p q} hp hq hne => ?_
    obtain ⟨a, b⟩ := p
    obtain ⟨c, d⟩ := q
    exact across (mem_pairs' hp) (mem_pairs' hq) hne

theorem norm_pList (ε : Fin n → Bool) : ∀ X ∈ pList ε, B X X = 1 := by
  intro X hX
  rw [pList_eq, List.mem_flatMap] at hX
  obtain ⟨⟨a, b⟩, hp, hX⟩ := hX
  exact norm_one (mem_pairs' hp) X hX

end GlobalTheory.TypeSum.CasBasis.PB

namespace GlobalTheory.TypeSum.CasBasis

theorem pB_orthonormal : ∀ (n : ℕ) (ε : Fin n → Bool) (a b : Fin (pList ε).length),
    (trace (pB ε a * pB ε b)).re = if a = b then 1 else 0 := by
  intro n ε a b
  have hpw := List.pairwise_iff_get.1 (PB.pairwise_pList ε)
  show PB.B (pB ε a) (pB ε b) = _
  rcases lt_trichotomy a b with h | rfl | h
  · rw [if_neg h.ne]; exact hpw a b h
  · rw [if_pos rfl]; exact PB.norm_pList ε _ (List.get_mem _ _)
  · rw [if_neg h.ne', PB.B_comm]; exact hpw b a h

end GlobalTheory.TypeSum.CasBasis

end
end
