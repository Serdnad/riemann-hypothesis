module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle314
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle315
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumInvarianceSupportTransportFrames
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalCongruenceSubgroupMemLevelTwistPrime
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle265
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GraphOfFixedGraph
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle183
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle110
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle285
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle317
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle278
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle316
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle011
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle274
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle282
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle304
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle065
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle281
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle291
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle297
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle303
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle233
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle012
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025
import Formalism.LocalToGlobal.KernelLattices.Bundle001
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

theorem _root_.GlobalTheory.T.functionalCondition_invariant_rightLevelTranslate : ∀ {D : Formalism.BasicNotions.D7} {X : Fields} (s : Seam D X) {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad) {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (P : ST) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (T : 𝓞 D.host.F) ∈ v.asIdeal) (ι : lev.fM v h →+ 𝓞 X.E ⧸ P.1.asIdeal) (y : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : lev.U) (d : Deco X.E (D.R.N i) ST SG), FunMoved s lev P v h ι y d → FunMoved s lev P v h ι (y * κ.1) d := by
  first | exact @GlobalTheory.funMoved_mul_level | exact GlobalTheory.funMoved_mul_level | (intros; apply GlobalTheory.funMoved_mul_level <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hostHomToColumnFieldHom_mem_twistedLattice_iff : ∀ {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ} (M : Submodule (𝓞 X.E) (HomE X.E a b)) (M' : Submodule (𝓞 D.host.E) (HomE D.host.E a b)), (∀ x, seamHom s x ∈ M ↔ x ∈ M') → ∀ (cl : ℕ) (e : HeightOneSpectrum (𝓞 X.E) → ℤ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℤ), (∀ P, e' (seamP s P) = e P) → ∀ x, seamHom s x ∈ twist₂ M cl e ↔ x ∈ twist₂ M' cl e' := by
  first | exact @GlobalTheory.SeamTwist.seamHom_mem_twO | exact GlobalTheory.SeamTwist.seamHom_mem_twO | (intros; apply GlobalTheory.SeamTwist.seamHom_mem_twO <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.sameCouplingCoset_invariant_frame_congruent_one : ∀ {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu) {n : ℕ} (κ : Sp X.E n ≃ₗ[X.E] Sp X.E n) (y0 : Sp X.E n), cst.Ok →
  κ ∈ GLint X.E n P.1 → (∀ w ∈ stdAt X.E n P.1, ((qOf P.1 : X.E) ^ cst.D P)⁻¹ • (κ w - w) ∈ stdAt X.E n P.1) →
  (P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) →
  (P.1 ∈ Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : X.E) * y0 l)) → (P.1 ∉ Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y0 l)) →
  ∀ w, SameCoset sel mu cst P (κ.symm w) y0 ↔ SameCoset sel mu cst P w y0 := by
  first | exact @GlobalTheory.CosetLoc.sameCoset_symm_iff | exact GlobalTheory.CosetLoc.sameCoset_symm_iff | (intros; apply GlobalTheory.CosetLoc.sameCoset_symm_iff <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

theorem _root_.GlobalTheory.T.transportedFrame_standardLocal_eq_localization : ∀ {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (g : Sp X.E n ≃ₗ[X.E] Sp X.E n) (N : Submodule (𝓞 X.E) (Sp X.E n)), (∀ x, g x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N ↔ x ∈ stdAt X.E n P) → mvL (seamGL s g) (stdAt D.host.E n (seamP s P)) = Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal (s.lat N) := by
  first | exact @GlobalTheory.FrameLat.seamGL_stdAt | exact GlobalTheory.FrameLat.seamGL_stdAt | (intros; apply GlobalTheory.FrameLat.seamGL_stdAt <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG


theorem _root_.GlobalTheory.T.coupledStep_localDatum_invariant_coset_move : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    ChIdx.Ok Ch sel mu cst L G m2 → ∀ (al : L.β m2) (P : rowSG Pr sel mu) (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (k : GLint X.E (R.N (m2 + 1)) P.1)
    (w w₁ : Sp X.E (R.N (m2 + 1))),
    (∀ s l, IntAt P.1 ((((qOf P.1 : ℕ) : X.E) ^ (cst.D P))⁻¹ * (k.1 (Pi.single s 1) l - (Pi.single s 1 : Sp X.E (R.N (m2 + 1))) l))) →
    SameCoset sel mu cst P (k.1.symm w₁) w →
    PsiAt Ch sel mu cst m2 P (L.h m2 al P) x₀ w₁ = PsiAt Ch sel mu cst m2 P (L.h m2 al P) x₀ w := by
  first | exact @GlobalTheory.PsiCosetInv.psiAt_coset | exact GlobalTheory.PsiCosetInv.psiAt_coset | (intros; apply GlobalTheory.PsiCosetInv.psiAt_coset <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_unitaryAut_columnField_of_standard_unitary_matrix : ∀ {D : D7} {X : Fields} (s : Seam D X), s.Ok → ∀ {n : ℕ} (G : GL (Fin n) D.host.E), cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (G : Matrix (Fin n) (Fin n) D.host.E) * (G : Matrix (Fin n) (Fin n) D.host.E) = 1 → ∃ g : UF X.E n, seamGL s g.1 = G := by
  first | exact @GlobalTheory.TwU.UnitaryFrom.exists_uf_seamGL_eq | exact GlobalTheory.TwU.UnitaryFrom.exists_uf_seamGL_eq | (intros; apply GlobalTheory.TwU.UnitaryFrom.exists_uf_seamGL_eq <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hostHomToColumnFieldHom_mem_periodLattice_iff : ∀ {D : D7} {X : Fields} (s : Seam D X), s.Ok → ∀ {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 X.E))) (cl : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), ∀ x : HomE D.host.E a b, seamHom s x ∈ perO (ambOf s B χ cD).AA N N' ↔ x ∈ perO (aaOf D cc) (s.lat N) (s.lat N') := by
  first | exact @GlobalTheory.TwV.SeamPer.seamHom_mem_perO | exact GlobalTheory.TwV.SeamPer.seamHom_mem_perO | (intros; apply GlobalTheory.TwV.SeamPer.seamHom_mem_perO <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finiteDatum_invariance_support_transport_frames : ∀ {D : D7} {X : Fields} (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (S : Finset (HeightOneSpectrum (𝓞 X.E))) {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (f : (Fin a → D.host.E) ≃ₗ[D.host.E] (Fin a → D.host.E)) (f' : (Fin b → D.host.E) ≃ₗ[D.host.E] (Fin b → D.host.E)) (cA cB : ℕ), 0 < cA → 0 < cB → ∀ (Ξ : HomE X.E a b → X.K), (∀ P ∈ S, Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 X.E) {r | ∃ c ∈ cc, ∃ t ∈ D.host.AA0, r = s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t)}) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E)) → (∀ x, Ξ x ≠ 0 → x ∈ divLat cA (homAt S N N')) → (∀ x, ∀ y ∈ mulLat cB (homAt S N N'), Ξ (x + y) = Ξ x) → DatLoc D cc (S.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) (cA * cB) ((s.lat N).map (f.toLinearMap.restrictScalars (𝓞 D.host.E))) ((s.lat N').map (f'.toLinearMap.restrictScalars (𝓞 D.host.E))) (fun z => s.σ₀ (Ξ (seamHom s (inFr f f' z)))) ∧ ∀ z, s.σ₀ (Ξ (seamHom s (inFr f f' z))) ≠ 0 → z ∈ divLat (cA * cB) (homAt (S.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) ((s.lat N).map (f.toLinearMap.restrictScalars (𝓞 D.host.E))) ((s.lat N').map (f'.toLinearMap.restrictScalars (𝓞 D.host.E)))) := by
  first | exact @GlobalTheory.DatTransport.datLoc_seam_inFr | exact GlobalTheory.DatTransport.datLoc_seam_inFr | (intros; apply GlobalTheory.DatTransport.datLoc_seam_inFr <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
open GlobalTheory.TopStep

theorem _root_.GlobalTheory.T.principal_congruence_subgroup_mem_level_twist_prime : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
    {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ},
    X.Ok → Pr.Ok → L.Ok Ch sel mu cst G m2 → ∀ {j : ℕ}, j ≤ m2 → ∀ (b : L.β j) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
    ∀ C : GLint X.E (R.N j) P.1, C ∈ GlobalTheory.TopStep.prinCong (R.N j) P.1 (cst.D P) →
    ∃ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) (L.h j b P),
      (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (C.1 x)) ∧
        chiInv Ch sel mu cst j P (L.h j b P) r = 1 := by
  first | exact @GlobalTheory.TwistCong.cong_mem_prCat_twist | exact GlobalTheory.TwistCong.cong_mem_prCat_twist | (intros; apply GlobalTheory.TwistCong.cong_mem_prCat_twist <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HeckeIso

section Abstract

variable {G V ι : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : G →* Module.End ℂ V} {Gv Gc : ι → Subgroup G}
  {J : Subgroup G}

theorem graph_of_local' (H : PlaceSys Gv Gc J) (horb : ∀ x, ((fun k => ρ k x) '' (J : Set G)).Finite)
    {S₁ S₂ : Submodule ℂ V} (h₁ : Irr ρ S₁) (h₂ : Irr ρ S₂) (n₁ : fixIn ρ J S₁ ≠ ⊥) (n₂ : fixIn ρ J S₂ ≠ ⊥)
    (hfd : FiniteDimensional ℂ (fixIn ρ J S₁)) (hloc : ∀ v, ∃ X, IsGraph ρ (Gv v) S₁ S₂ X) :
    ∃ W, IsGraph ρ ⊤ S₁ S₂ W := by
  obtain ⟨X, hX0, hXm, hX, i₁, i₂⟩ := GlobalTheory.T.exists_stable_graph_of_equal_annihilators V ι (fun v => locAlg ρ (Gv v) (Gc v) ⊓ fixAlg ρ J)
    (fixIn ρ J S₁) (fixIn ρ J S₂) hfd n₁ n₂
    (fun v c hc x hx => ⟨locAlg_mem hc.1 h₁.stab hx.1, hc.2 x hx.2⟩)
    (fun v c hc x hx => ⟨locAlg_mem hc.1 h₂.stab hx.1, hc.2 x hx.2⟩)
    (fun v w hvw c hc d hd => ⟨fun x _ => locAlg_comm (H.le v w hvw) hc.1 hd.1 x,
      fun x _ => locAlg_comm (H.le v w hvw) hc.1 hd.1 x⟩)
    (fun v c hc => by
      obtain ⟨P, hP⟩ := exists_avg ρ (Gv v ⊓ J) fun x => (horb x).subset (Set.image_mono fun k hk => hk.2)
      obtain ⟨Q, hQ⟩ := exists_avg ρ (Gc v ⊓ J) fun x => (horb x).subset (Set.image_mono fun k hk => hk.2)
      obtain ⟨X, hX⟩ := hloc v
      exact ⟨ann_transfer (H.comm v) (H.dec v) (H.decJ v) hP hQ h₁ h₂ n₁ hX hc.1,
        ann_transfer (H.comm v) (H.dec v) (H.decJ v) hP hQ h₂ h₁ n₂ hX.swap hc.1⟩)
    (fun Y hY hst => fixIn_simple H horb h₁ Y hY hst) (fun Y hY hst => fixIn_simple H horb h₂ Y hY hst)
  exact graph_of_fixed_graph H horb h₁ h₂ n₁ n₂ X hX0 hXm hX i₁ i₂

theorem graph_of_local (H : PlaceSys Gv Gc J) {S₁ S₂ : Submodule ℂ V} (h₁ : Irr ρ S₁) (h₂ : Irr ρ S₂)
    (horb : ∀ x ∈ S₁ ⊔ S₂, ((fun k => ρ k x) '' (J : Set G)).Finite)
    (n₁ : fixIn ρ J S₁ ≠ ⊥) (n₂ : fixIn ρ J S₂ ≠ ⊥)
    (hfd : FiniteDimensional ℂ (fixIn ρ J S₁)) (hloc : ∀ v, ∃ X, IsGraph ρ (Gv v) S₁ S₂ X) :
    ∃ W, IsGraph ρ ⊤ S₁ S₂ W := by
  have hne : ∀ S ≤ S₁ ⊔ S₂, fixIn ρ J S ≠ ⊥ →
      fixIn (res ρ _ (sup_stab h₁ h₂)) J (S.comap (S₁ ⊔ S₂).subtype) ≠ ⊥ := by
    intro S hS h
    obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    exact (Submodule.ne_bot_iff _).2 ⟨⟨f, hS hf.1⟩, ⟨hf.1, fun k hk => Subtype.ext (hf.2 k hk)⟩,
      fun e => hf0 (congrArg Subtype.val e)⟩
  obtain ⟨W, hW⟩ := graph_of_local' (ρ := res ρ _ (sup_stab h₁ h₂)) H (orbit_res horb) (h₁.res le_sup_left)
    (h₂.res le_sup_right) (hne _ le_sup_left n₁) (hne _ le_sup_right n₂)
    (FiniteDimensional.of_injective
      (((S₁ ⊔ S₂).subtype.comp (fixIn (res ρ _ (sup_stab h₁ h₂)) J (S₁.comap (S₁ ⊔ S₂).subtype)).subtype).codRestrict
        (fixIn ρ J S₁) (fun f => ⟨f.2.1, fun k hk => congrArg Subtype.val (f.2.2 k hk)⟩))
      (fun a b e => by
        have e' := congrArg Subtype.val e
        exact Subtype.ext (Subtype.ext e')))
    (fun v => by
      obtain ⟨X, hX⟩ := hloc v
      exact ⟨_, hX.res le_sup_left le_sup_right⟩)
  exact ⟨_, hW.of_res⟩

end Abstract

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

def rtRep (W : Type) [AddCommGroup W] [Module ℂ W] : GAf L n →* Module.End ℂ (GAf L n → W) where
  toFun g := NG.rt L n g
  map_one' := LinearMap.ext fun φ => funext fun x => by
    show φ (x * 1) = φ x
    rw [mul_one]
  map_mul' g g' := LinearMap.ext fun φ => funext fun x => by
    show φ (x * (g * g')) = φ (x * g * g')
    rw [mul_assoc]

def Gaway (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : Subgroup (GAf L n) where
  carrier := {x | TrivOutside {v}ᶜ x}
  mul_mem' := fun hx hy => GlobalTheory.SatInd.CosetFin.trivOutside_mul hx hy
  one_mem' := GlobalTheory.InertSph.trivOutside_one _
  inv_mem' := fun hx => GlobalTheory.SatInd.CosetFin.trivOutside_inv hx

theorem placeSys {N : ℕ} (hN : 0 < N) :
    PlaceSys (GlobalTheory.InertSph.Gv L n) (Gaway L n) (GlobalTheory.IsotOrth.congSub L n N) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun v x hx y hy => (GlobalTheory.InertSph.commute_of_trivOutside v x y hx hy).eq
  · intro v w hvw x hx u hu
    apply hx u
    have : u = v := by simpa using hu
    subst this
    simpa using hvw
  · intro v g
    obtain ⟨x, y, hx, hy, e⟩ := GlobalTheory.T.finiteAdelicUnitary_eq_mul_trivOutside_place_and_at_place L n v g
    exact ⟨x, hx, y, hy, e⟩
  · intro v k hk
    obtain ⟨x, y, hx, hy, cx, cy, e⟩ := GlobalTheory.T.principalCongruence_split_trivOutside_and_at_place L n N v k hk
    exact ⟨x, ⟨hx, cx⟩, y, ⟨hy, cy⟩, e⟩
  · exact fun p h1 h2 => GlobalTheory.T.finiteAdelicGL_induction_over_places L n N hN p h1 (fun v x y hx hy => h2 v x hx y hy)

variable {L n}

theorem irr_of {a : NG.AlgWt L n} {S : Submodule ℂ (GAf L n → a.W)} (h : NG.IsIrrRep a.ρ S) :
    Irr (rtRep L n a.W) S :=
  ⟨h.1.stable, fun T hT hst => h.2.2 T ⟨hT.trans h.1.le, hst⟩ hT⟩

theorem orbit_fin {a : NG.AlgWt L n} {S₁ S₂ : Submodule ℂ (GAf L n → a.W)} (h₁ : NG.IsIrrRep a.ρ S₁)
    (h₂ : NG.IsIrrRep a.ρ S₂) {K : Subgroup (GAf L n)} (hK : K ≤ Umax L n) :
    ∀ x ∈ S₁ ⊔ S₂, ((fun k => rtRep L n a.W k x) '' (K : Set (GAf L n))).Finite := by
  intro x hx
  obtain ⟨N, hN, hx⟩ := (sup_le h₁.1.le h₂.1.le hx).2
  exact (GlobalTheory.IsotOrth.orbit_finite (rtRep L n a.W) hN x fun κ hκ => funext fun g => hx κ hκ g).subset
    (Set.image_mono hK)

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S₁ S₂ : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S₁ → NG.IsIrrRep a.ρ S₂ → (∀ s : SplitPlace L, ∃ σ₁ σ₂ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)), IsLocS S₁ s σ₁ ∧ IsLocS S₂ s σ₂ ∧ Nonempty (σ₁.ρ.Equiv σ₂.ρ)) → (∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)), (∀ s : SplitPlace L, s.v ≠ v) → ∃ (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.OverPl w v ∧ (∃ f ∈ S₁, f ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) ∧ (∃ f ∈ S₂, f ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) ∧ ∀ U : Subgroup (GAf L n), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), (∀ f ∈ S₁, (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv h f = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • f) ∧ (∀ f ∈ S₂, (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv h f = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • f)) → ∀ N : ℕ, 0 < N → (∃ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) ∧ f ≠ 0) → ∃ φ : (GAf L n → a.W) →ₗ[ℂ] (GAf L n → a.W), (∀ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) → φ f ∈ S₂ ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ (φ f) = φ f) ∧ (∃ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) ∧ φ f ≠ 0) ∧ (∀ (g : GAf L n) (f : GAf L n → a.W), f ∈ S₁ → (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) → φ (NG.heckeD (GlobalTheory.IsotOrth.congSub L n N) {x | ∃ u ∈ GlobalTheory.IsotOrth.congSub L n N, ∃ u' ∈ GlobalTheory.IsotOrth.congSub L n N, x = u * g * u'} f) = NG.heckeD (GlobalTheory.IsotOrth.congSub L n N) {x | ∃ u ∈ GlobalTheory.IsotOrth.congSub L n N, ∃ u' ∈ GlobalTheory.IsotOrth.congSub L n N, x = u * g * u'} (φ f)) := by
  intro L _ _ _ n a S₁ S₂ h₁ h₂ hsplit hinert N hN hf
  refine GlobalTheory.T.exists_doubleCosetCommuting_map_principalCongruence L n a S₁ S₂ h₁ ?_ N hN hf
  obtain ⟨g₁, hg₁, hg₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₁.2.1
  obtain ⟨g₂, hg₂, hg₂0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₂.2.1
  obtain ⟨M₁, hM₁, e₁⟩ := (h₁.1.le hg₁).2
  obtain ⟨M₂, hM₂, e₂⟩ := (h₂.1.le hg₂).2
  have hM : 0 < M₁ * M₂ := Nat.mul_pos hM₁ hM₂
  have H := placeSys L n hM
  haveI : FiniteDimensional ℂ a.W := a.alg.1
  obtain ⟨W, hW⟩ := graph_of_local H (irr_of h₁) (irr_of h₂) (orbit_fin h₁ h₂ fun k hk => hk.1)
    ((Submodule.ne_bot_iff _).2 ⟨g₁, ⟨hg₁, fun k hk => funext fun g => e₁ k (NG.Cong.of_mul_left L n hk) g⟩, hg₁0⟩)
    ((Submodule.ne_bot_iff _).2 ⟨g₂, ⟨hg₂, fun k hk => funext fun g => e₂ k (NG.Cong.of_mul_right L n hk) g⟩, hg₂0⟩)
    (by
      have := GlobalTheory.AlgFormsFin.fixedForms_finite L n a.ρ (GlobalTheory.T.finite_doubleCosets_definiteUnitary_maximalLevel L n) hM
      refine Submodule.finiteDimensional_of_le (S₂ := GlobalTheory.AlgFormsFin.fixedForms L n a.ρ (M₁ * M₂)) ?_
      rintro f ⟨hfS, hfU⟩
      exact ⟨(h₁.1.le hfS).1, fun κ hκ g => congrFun (hfU κ hκ) g⟩)
    (fun v => by
      by_cases hv : ∃ s : SplitPlace L, s.v = v
      · obtain ⟨s, rfl⟩ := hv
        obtain ⟨σ₁, σ₂, l₁, l₂, he⟩ := hsplit s
        obtain ⟨X, x1, x2, x3, x4, x5⟩ := GlobalTheory.T.exists_stable_graph_of_iso_splitPlace_components L n a S₁ S₂ s σ₁ σ₂ l₁ l₂ he
        exact ⟨X, x1, x2, x3, x4, x5⟩
      · obtain ⟨w, Dv, α, -, ⟨f₁, hf₁, n₁, k₁⟩, ⟨f₂, hf₂, n₂, k₂⟩, hH⟩ := hinert v fun s hs => hv ⟨s, hs⟩
        refine graph_of_hecke (K := GlobalTheory.InertSph.Kv L n v) (H.comm v) (H.dec v) inf_le_right (irr_of h₁) (irr_of h₂)
          (orbit_fin h₁ h₂ inf_le_left) hf₁ hf₂ n₁ n₂ (fun k hk => k₁ k hk.1 hk.2) (fun k hk => k₂ k hk.1 hk.2)
          fun x hx => ?_
        obtain ⟨R, h, hR, hh, hA⟩ := GlobalTheory.T.inertDoubleCosetOperator_eq_inertHeckeOperator L n v w Dv (GlobalTheory.T.inertDatum_local_mem_unitaryGroup_antidiagonal L n v w Dv) (GlobalTheory.T.inertDatum_local_stdLatticeStabilizer_mem_maxCompact L n v w Dv)
          (GlobalTheory.T.exists_trivOutside_inertDatum_local_eq L n v w Dv) (GlobalTheory.T.inertDatum_local_injective_on_trivOutside L n v w Dv) x hx
        have hK : ∀ κ : GAf L n, κ ∈ Umax L n → TrivOutside {v} κ → ∃ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n,
            (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n :=
          fun κ hκ _ => ⟨GlobalTheory.T.inertDatum_local_mem_unitaryGroup_antidiagonal L n v w Dv κ, GlobalTheory.T.inertDatum_local_stdLatticeStabilizer_mem_maxCompact L n v w Dv κ hκ _⟩
        have hKv : ∀ κ : GAf L n, TrivOutside {v} κ → (κ ∈ GlobalTheory.InertSph.Kv L n v ↔ κ ∈ Umax L n) :=
          fun κ hκ => ⟨fun h => h.1, fun h => ⟨h, hκ⟩⟩
        obtain ⟨γ, ⟨hγ, -⟩, -⟩ := hR.2 x ⟨1, one_mem _, 1, one_mem _, by simp⟩
        refine ⟨R, Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α, ⟨γ, hγ⟩, hR.1, ?_, ?_⟩
        · refine (hA a.W f₁ k₁).trans ?_
          rw [GlobalTheory.T.inertHeckeOperator_level_independent L n v w Dv hK (Umax L n) _ (fun _ _ => Iff.rfl) hKv a.W h hh.1 f₁ k₁]
          exact (hH _ hKv h hh).1 f₁ hf₁ fun k hk => k₁ k hk.1 hk.2
        · refine (hA a.W f₂ k₂).trans ?_
          rw [GlobalTheory.T.inertHeckeOperator_level_independent L n v w Dv hK (Umax L n) _ (fun _ _ => Iff.rfl) hKv a.W h hh.1 f₂ k₂]
          exact (hH _ hKv h hh).2 f₂ hf₂ fun k hk => k₂ k hk.1 hk.2)
  exact GlobalTheory.T.equivariant_iso_of_translationStable_graph L n a.ρ a.ρ S₁ S₂ W h₁ h₂ hW.mem (fun h w hw => hW.stab h trivial w hw) hW.inj₁ hW.inj₂ hW.ne

end GlobalTheory.HeckeIso
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil


noncomputable section

namespace GlobalTheory

theorem isSubquotient_prod₂_of_cuspSupport_reorder : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.UnlinkedProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t s : ℕ) (π : Irr k (r + t)) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)) (S : Finset (Fin s)), IsCuspSupport π.π d (fun a => (σ a).π) → (∀ b ∈ S, d b = 1) → (∀ a b, a ∉ S → b ∈ S → ∀ (h : d a = d b) (α : ℂˣ), ¬ Nonempty ((h ▸ σ a : Irr k (d b)).π.Equiv (_root_.GlobalTheory.SmGL.twist (σ b).π (detChar (Fin (d b)) (unrChar k α))))) → ∑ a ∈ Sᶜ, d a = r → ∑ a ∈ S, d a = t → ∃ (s₁ s₂ : ℕ) (ι₁ : Fin s₁ → Fin s) (ι₂ : Fin s₂ → Fin s) (e₁ : (Σ a, Fin (d (ι₁ a))) ≃ Fin r) (e₂ : (Σ b, Fin (d (ι₂ b))) ≃ Fin t) (V₁ V₂ : Type) (_ : AddCommGroup V₁) (_ : Module ℂ V₁) (_ : AddCommGroup V₂) (_ : Module ℂ V₂) (ρ₁ : Representation ℂ (GL (Fin r) k) V₁) (ρ₂ : Representation ℂ (GL (Fin t) k) V₂), (∀ a, ι₁ a ∉ S) ∧ (∀ b, ι₂ b ∈ S) ∧ IsSmooth ρ₁ ∧ IsSmooth ρ₂ ∧ Nonempty (ρ₁.Equiv (multiProd e₁ fun a => (σ (ι₁ a)).π)) ∧ Nonempty (ρ₂.Equiv (multiProd e₂ fun b => (σ (ι₂ b)).π)) ∧ IsSubquotient π.π (prod₂ ρ₁ ρ₂) := by
  intro hBZ hGL hUPI k _ _ _ _ r t s π d σ S hsupp hS hunl hr ht
  obtain ⟨-, hσ, e, hsub⟩ := hsupp
  have sumc : ∀ (T : Finset (Fin s)), ∑ a : Fin T.card, d (T.orderEmbOfFin rfl a) = ∑ a ∈ T, d a := by
    intro T
    rw [← Finset.sum_coe_sort T]
    exact Fintype.sum_equiv (T.orderIsoOfFin rfl).toEquiv _ _ (fun a => by simp)
  have c₁ : Fintype.card (Σ a : Fin Sᶜ.card, Fin (d (Sᶜ.orderEmbOfFin rfl a))) = Fintype.card (Fin r) := by
    simp [Fintype.card_sigma, sumc, hr]
  have c₂ : Fintype.card (Σ b : Fin S.card, Fin (d (S.orderEmbOfFin rfl b))) = Fintype.card (Fin t) := by
    simp [Fintype.card_sigma, sumc, ht]
  let e₁ := Fintype.equivOfCardEq c₁
  let e₂ := Fintype.equivOfCardEq c₂
  obtain ⟨φ⟩ := GlobalTheory.T.parabolicProduct_equiv_product_of_partition k s d σ S r t e e₁ e₂ (fun a b ha hb n _ _ f f' =>
    GlobalTheory.T.cuspidal_pair_irreducible_product hBZ hGL hUPI k n (fun i => d (![a, b] i)) (fun i => σ (![a, b] i))
      (fun i => ⟨(hσ _).1, (hσ _).2.2⟩) (hS b hb) (hunl a b ha hb) f f')
  refine ⟨Sᶜ.card, S.card, fun a => Sᶜ.orderEmbOfFin rfl a, fun b => S.orderEmbOfFin rfl b, e₁, e₂, _, _,
    inferInstance, inferInstance, inferInstance, inferInstance,
    multiProd e₁ fun a => (σ (Sᶜ.orderEmbOfFin rfl a)).π, multiProd e₂ fun b => (σ (S.orderEmbOfFin rfl b)).π,
    fun a => Finset.mem_compl.1 (Finset.orderEmbOfFin_mem Sᶜ rfl a),
    fun b => Finset.orderEmbOfFin_mem S rfl b, isSmooth_parInd _ _, isSmooth_parInd _ _,
    ⟨Representation.Equiv.refl _⟩, ⟨Representation.Equiv.refl _⟩, ?_⟩
  exact hsub.trans (IsSubquotient.of_surjective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.surjective)

end GlobalTheory

end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut

namespace GlobalTheory.RoadW

theorem sphAt_of_repIso {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (π : CuspSub E a) {r r' : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)}
    (hr : Continuous r) (hiso : UpperTheory.V.Af.RepIso r r') (c : GlobalTheory.RoadU.Sph) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ)
    (hc : GlobalTheory.RoadU.SphAt c π ι r w B) : GlobalTheory.RoadU.SphAt c π ι r' w B := by
  cases c with
  | unr =>
    obtain ⟨p, hp⟩ := hiso
    intro hl A hA
    obtain ⟨h1, h2⟩ := hc hl A hA
    refine ⟨fun s hs => by rw [hp, h1 s hs]; group, fun σ hσ => ?_⟩
    rw [← h2 σ hσ, hp, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
  | dR => exact clauseAt_of_repIso E Ω l ι a π r r' hr hiso .dR w hc
  | crys => exact clauseAt_of_repIso E Ω l ι a π r r' hr hiso .crys w hc
  | phi =>
    obtain ⟨p, hp⟩ := hiso
    have hcd : ∀ (A : ValuationSubring Ω) (g : ↥(_root_.ReciprocityTheory.Gal.Dec (F := E) A)), r'.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype g =
        p * r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype g * p⁻¹ := fun A g => hp g
    intro P AI hT A h O _ _ _ Bw hj g
    have e := GlobalTheory.AboveL.RepConj.wdAt_conj P ι Bw h hj p (hcd A)
    exact (congrArg (fun x => WD.charPol x g) e).trans (hc P AI hT A h O Bw hj g)

theorem core_of_rowStarCore : GlobalTheory.RoadW.RowStarCore → GlobalTheory.RoadU.Core := by
  intro h
  refine ⟨fun E Ω _ _ _ _ _ _ l _ ι a ha π χ hs => ?_, fun c E Ω _ _ _ _ _ _ l _ ι a ha π χ hs r hr w _ B hB => ?_⟩
  · obtain rfl : χ = quadChar E ^ a := hs.2.2.2
    obtain ⟨r, hr, -⟩ := h E Ω l ι a ha π hs
    exact ⟨r, hr⟩
  · obtain rfl : χ = quadChar E ^ a := hs.2.2.2
    obtain ⟨r₀, hr₀, hc⟩ := h E Ω l ι a ha π hs
    refine sphAt_of_repIso ι π hr₀.1 (weak_repIso E Ω l ι a π r₀ r hr₀ hr) c w B ?_
    obtain ⟨h1, h2, h3, h4⟩ := hc w B hB
    cases c
    exacts [h1, h2, h3, h4]

end GlobalTheory.RoadW
end
