module

public import Formalism.AlgebraicWeights.IsAlgWeight
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle002
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain Module Module.End

namespace Formalism.L2.NCov

variable {O K V : Type*} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] {S : Set (End K V)} [IsLocalRing O]

end Formalism.L2.NCov

namespace Formalism.L2

variable {D : D7} {M : MtFam D}

def SplitEx (D : D7) : Prop :=
  ∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ

end Formalism.L2
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain Module Module.End

namespace Formalism.L2

def placesS (D : D7) (l : ℕ) : Set (PlE D.host) :=
  {v | (v ∈ placesOver D.host.E (D.host.g 0) ∨ v ∈ placesOver D.host.E (D.host.g 1) ∨
      v ∈ placesOver D.host.E (if l = D.host.pde then D.host.pde' else D.host.pde)) ∧
    v ∉ placesOver D.host.E l}

def GenAt (D : D7) (l : ℕ) (Q : Finset (PlE D.host)) (v : PlE D.host) (k : ℕ) : Prop :=
  IsSplitPl D.host v ∧ v ∉ placesOver D.host.E l ∧ v ∉ placesS D l ∧ v ∉ Q ∧ 1 ≤ k ∧ k ≤ D.R.nV

theorem mtL_eq (D : D7) {j : ℕ} {w : D.what₂.places.Pl} {i : D.nd.Loc} (h : i ∈ D.nd.locs j w) :
    D.what₂.MtL (D.nd.mu i) (D.nd.j i) = D.what₂.MtL (D.what₂.muTw w) j := by
  obtain ⟨h1, h2⟩ := (D.nd.locs_mem j w i).1 h
  rw [D.nd.mu_w i, h1, h2]

def castMt (D : D7) {j : ℕ} {w : D.what₂.places.Pl} {i : D.nd.Loc} (h : i ∈ D.nd.locs j w)
    (x : D.what₂.MtL (D.nd.mu i) (D.nd.j i)) : D.what₂.MtL (D.what₂.muTw w) j :=
  cast (mtL_eq D h) x

def castMtInv (D : D7) {j : ℕ} {w : D.what₂.places.Pl} {i : D.nd.Loc} (h : i ∈ D.nd.locs j w)
    (y : D.what₂.MtL (D.what₂.muTw w) j) : D.what₂.MtL (D.nd.mu i) (D.nd.j i) :=
  cast (mtL_eq D h).symm y

theorem castMt_castMtInv (D : D7) {j : ℕ} {w : D.what₂.places.Pl} {i : D.nd.Loc} (h : i ∈ D.nd.locs j w)
    (y : D.what₂.MtL (D.what₂.muTw w) j) : castMt D h (castMtInv D h y) = y := by
  unfold castMt castMtInv
  exact cast_cast _ _ y



structure NLocBase (D : D7) (M : MtFam D) where

  Oc : ℕ → D.what₂.places.Pl → Type
  [ringOc : ∀ j w, CommRing (Oc j w)]
  [domOc : ∀ j w, IsDomain (Oc j w)]
  [dvrOc : ∀ j w, IsDiscreteValuationRing (Oc j w)]

  ec : ∀ j w, D.what₂.LL →+* FractionRing (Oc j w)

  ec_w : ∀ j w (x : D.what₂.LL), 0 ≤ D.what₂.places.val w x ↔
    ec j w x ∈ (algebraMap (Oc j w) (FractionRing (Oc j w))).range

  V : ℕ → D.what₂.places.Pl → Type
  [acgV : ∀ j w, AddCommGroup (V j w)]
  [modV : ∀ j w, Module (FractionRing (Oc j w)) (V j w)]
  [modVO : ∀ j w, Module (Oc j w) (V j w)]
  [towV : ∀ j w, IsScalarTower (Oc j w) (FractionRing (Oc j w)) (V j w)]
  iV : ∀ j w, D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[ec j w] V j w

  iV_basis : ∀ j w (b : Module.Basis (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
      D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)),
    LinearIndependent (FractionRing (Oc j w)) (fun a => iV j w (b a)) ∧
      Submodule.span (FractionRing (Oc j w)) (Set.range fun a => iV j w (b a)) = ⊤

  Qc : ℕ → D.what₂.places.Pl → Finset (PlE D.host)

  hL : ∀ j w, PlE D.host → ℕ → Module.End D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)

  hL_def : ∀ j w (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (v : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
    GenAt D (D.what₂.places.resChar w) (Qc j w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ →
    ∀ x, (M (D.what₂.muTw w) j h1 h2).real (D.what₂.jMt (D.what₂.muTw w) j (hL j w v k x)) =
      NG.tN (M (D.what₂.muTw w) j h1 h2).J s ϖ k ((M (D.what₂.muTw w) j h1 h2).real (D.what₂.jMt (D.what₂.muTw w) j x))

  hK : ∀ j w, PlE D.host → ℕ → Module.End (FractionRing (Oc j w)) (V j w)
  hK_def : ∀ j w v k x, hK j w v k (iV j w x) = iV j w (hL j w v k x)

  split : ∀ j w v k, GenAt D (D.what₂.places.resChar w) (Qc j w) v k →
    ⨆ μ, (hK j w v k).maxGenEigenspace μ = ⊤

  Qc_over : ∀ j w (v v' : PlE D.host), v ∈ Qc j w →
    (∃ v₀ : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)), NG.OverPl v v₀ ∧ NG.OverPl v' v₀) → v' ∈ Qc j w

  Qc_conj : ∀ j w (v v' : PlE D.host), v' ∈ Qc j w → IsConjPl D.host v v' → v ∈ Qc j w

attribute [instance] NLocBase.ringOc NLocBase.domOc NLocBase.dvrOc NLocBase.acgV NLocBase.modV
  NLocBase.modVO NLocBase.towV

def heckeGens {D : D7} {M : MtFam D} (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) :
    Set (Module.End (FractionRing (B.Oc j w)) (B.V j w)) :=
  {f | ∃ v k, GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k ∧ f = B.hK j w v k}

abbrev heckeAlg {D : D7} {M : MtFam D} (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) :
    Subalgebra (B.Oc j w) (Module.End (FractionRing (B.Oc j w)) (B.V j w)) :=
  Algebra.adjoin (B.Oc j w) (heckeGens B j w)



structure NormalizedLocalCompatibility (D : D7) (M : MtFam D) where
  B : NLocBase D M

  Q_eq : ∀ j w i, i ∈ D.nd.locs j w → D.nd.Q i = B.Qc j w

  mx : ∀ j w, D.nd.Loc → Ideal (heckeAlg B j w)
  mx_max : ∀ j w i, i ∈ D.nd.locs j w → (mx j w i).IsMaximal

  mx_inj : ∀ j w, Set.InjOn (mx j w) (D.nd.locs j w)

  mx_all : ∀ j w, 1 ≤ j → j ≤ D.R.m → D.what₂.muAt w ≠ D.what₂.mu0 → ∀ I : Ideal (heckeAlg B j w), I.IsMaximal →
    ∃ i ∈ D.nd.locs j w, mx j w i = I

  phO : ∀ j w i, i ∈ D.nd.locs j w → D.nd.O i ≃+* B.Oc j w
  phK : ∀ j w i, i ∈ D.nd.locs j w → FractionRing (D.nd.O i) ≃+* FractionRing (B.Oc j w)
  phK_alg : ∀ j w i (h : i ∈ D.nd.locs j w) (z : D.nd.O i),
    phK j w i h (algebraMap _ _ z) = algebraMap _ _ (phO j w i h z)
  phK_emb : ∀ j w i (h : i ∈ D.nd.locs j w) (x : D.what₂.LL), phK j w i h (D.nd.embK i x) = B.ec j w x

  Psi : ∀ j w i (h : i ∈ D.nd.locs j w),
    TensorProduct (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i) →ₛₗ[(phK j w i h).toRingHom] B.V j w
  Psi_inj : ∀ j w i (h : i ∈ D.nd.locs j w), Function.Injective (Psi j w i h)
  Psi_range : ∀ j w i (h : i ∈ D.nd.locs j w) (y : B.V j w),
    y ∈ NCov.part (heckeAlg B j w) (mx j w i) ↔ ∃ z, Psi j w i h z = y

  Psi_pr : ∀ j w i (h : i ∈ D.nd.locs j w) (x : D.what₂.MtL (D.nd.mu i) (D.nd.j i)),
    Psi j w i h (D.nd.prMt i x) - B.iV j w (castMt D h x) ∈ NCov.off (heckeAlg B j w) (mx j w i)

  ptX : ∀ j w i (h : i ∈ D.nd.locs j w), D.nd.X i ≃
    {ψ : heckeAlg B j w →ₐ[B.Oc j w] B.Oc j w //
      NCov.cls ψ = mx j w i ∧ NCov.W (heckeAlg B j w) (NCov.pt ψ) ≠ ⊥}

  ptX_hT : ∀ j w i (h : i ∈ D.nd.locs j w) (x : D.nd.X i) (v : PlE D.host) (k : ℕ)
    (hvk : GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k),
    phO j w i h ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x) =
      (ptX j w i h x).1 ⟨B.hK j w v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩

  iotaC : ∀ j w, B.Oc j w →+* ℂ

  iotaC_coh : ∀ j w i (h : i ∈ D.nd.locs j w) (z : D.nd.O i), iotaOC D i z = iotaC j w (phO j w i h z)

def HeckeStd {D : D7} {M : MtFam D} (B : NLocBase D M) : Prop :=
  ∀ j w, 1 ≤ j → j ≤ D.R.m →
    (∀ v k v' k', GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k →
      GenAt D (D.what₂.places.resChar w) (B.Qc j w) v' k' → Commute (B.hK j w v k) (B.hK j w v' k')) ∧
    (∀ v k, GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → ∀ μ, (B.hK j w v k).maxGenEigenspace μ ≠ ⊥ →
      μ ∈ (algebraMap (B.Oc j w) (FractionRing (B.Oc j w))).range)

def LocPl (D : D7) (j : ℕ) (w : D.what₂.places.Pl) : Prop :=
  D.what₂.muAt w ≠ D.what₂.mu0 ∨ (D.nd.locs j w).Nonempty

theorem locPl_of_mem (D : D7) {j : ℕ} {w : D.what₂.places.Pl} {i : D.nd.Loc} (h : i ∈ D.nd.locs j w) :
    LocPl D j w :=
  Or.inr ⟨i, h⟩

def HeckeStdTw {D : D7} {M : MtFam D} (B : NLocBase D M) : Prop :=
  ∀ j w, 1 ≤ j → j ≤ D.R.m → LocPl D j w →
    (∀ v k v' k', GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k →
      GenAt D (D.what₂.places.resChar w) (B.Qc j w) v' k' → Commute (B.hK j w v k) (B.hK j w v' k')) ∧
    (∀ v k, GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → ∀ μ, (B.hK j w v k).maxGenEigenspace μ ≠ ⊥ →
      μ ∈ (algebraMap (B.Oc j w) (FractionRing (B.Oc j w))).range)

theorem heckeStdTw_of_std {D : D7} {M : MtFam D} {B : NLocBase D M} (h : HeckeStd B) : HeckeStdTw B :=
  fun j w h1 h2 _ => h j w h1 h2

end Formalism.L2
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual NumberField IsDedekindDomain Polynomial

namespace Formalism.L2.NR

section frame

variable {E Ω L : Type} [Field E] [Field Ω] [Algebra E Ω] [Field L]

end frame

def IsRepOfSigI (D : D7) (ℓ : ℕ) [Fact ℓ.Prime] (ι : Qbar ℓ ≃+* ℂ) (b : ℕ) (Sig : List (Formalism.BasicNotions.Part D.naut.CG))
    (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin b) (Qbar ℓ)) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin b) (Qbar ℓ)) : Matrix (Fin b) (Fin b) (Qbar ℓ))) ∧
  Formalism.MainNotions.N.IsSSRep ρ ∧
  ∀ᶠ w in Filter.cofinite, ∀ (B : ValuationSubring D.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om),
    IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
    ((ρ σ : GL _ _) : Matrix (Fin b) (Fin b) (Qbar ℓ)).charpoly.map ι.toRingHom =
      Formalism.MainNotions.N.galPol D.naut (D.naut.lpTw (Formalism.MainNotions.N.isoLoc D.nd D.naut Sig w) ((1 - (b : ℝ)) / 2))

def IsRepOfSigQ (D : D7) (i : D.nd.Loc) (b : ℕ) (Sig : List (Formalism.BasicNotions.Part D.naut.CG))
    (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin b) (Qbar (D.nd.l i))) : Prop :=
  IsRepOfSigI D (D.nd.l i) (D.naut.iotaQC i) b Sig ρ

def twistRep {Γ K : Type} [Group Γ] [CommRing K] {n : ℕ} (ρ : Γ →* GL (Fin n) K) (χ : Γ →* Kˣ) :
    Γ →* GL (Fin n) K where
  toFun g := Units.map (algebraMap K (Matrix (Fin n) (Fin n) K)).toMonoidHom (χ g) * ρ g
  map_one' := by simp
  map_mul' g h := by
    have key : ∀ (c : K) (M : Matrix (Fin n) (Fin n) K),
        (algebraMap K (Matrix (Fin n) (Fin n) K)).toMonoidHom c * M = M * (algebraMap K (Matrix (Fin n) (Fin n) K)).toMonoidHom c :=
      fun c M => Algebra.commutes c M
    ext1
    simp only [map_mul, Units.val_mul, Units.coe_map, mul_assoc]
    congr 1
    rw [← mul_assoc, ← mul_assoc, ← key]

def IsConjRep {Γ K : Type} [Group Γ] [CommRing K] {n : ℕ} (ρ₁ ρ₂ : Γ →* GL (Fin n) K) : Prop :=
  ∃ P : GL (Fin n) K, ∀ g, ρ₁ g = P * ρ₂ g * P⁻¹

theorem one_le_r (D : D7) : 1 ≤ D.R.r := by
  have := D.R.two_le_m
  show 1 ≤ D.R.k + D.R.m - 1
  omega

def GalRepEx (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (a : ℕ), 1 ≤ a → ∀ π : D.naut.CG a, D.naut.csd π → D.naut.ralg π →
    ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i)), IsRepOfSigQ D i a [⟨a, π, 1⟩] ρ

def ClassFieldHeckeAlgebraic (D : D7) : Prop :=
  ∀ i (χ : D.naut.CG 1) (s : ℝ), (∀ τ : D.host.E →+* ℂ, ∀ z ∈ D.naut.infG χ τ, ∃ k : ℤ, z + (s : ℂ) = (k : ℂ)) →
    ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i)), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ ∧
      (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG χ w) s) ∧
      ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG χ w) s ∧
        ∀ τ, Formalism.MainNotions.N.InducesW D.nd i τ w → (D.naut.jumpsW i ρ τ).map (fun n : ℤ => (n : ℂ)) =
          (D.naut.infG χ ((D.naut.iotaQC i).toRingHom.comp τ)).map (fun z => -(z + (s : ℂ)))

def EtaShiftInt (D : D7) : Prop :=
  ∀ τ : D.host.E →+* ℂ, ∀ z ∈ D.naut.infG D.naut.etaTinv τ, ∃ k : ℤ, z + ((-(D.R.t : ℝ) / 2 : ℝ) : ℂ) = (k : ℂ)

def RowPar (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (σ : D.what₂.FT), D.what₂.isot (D.nd.j i) σ ≠ ⊥ → ∃ Sig : List (Part D.naut.CG),
    Formalism.MainNotions.N.HasParamW D.nd D.naut i σ Sig ∧ (D.nd.goodRow σ → ∀ p ∈ Sig, D.naut.csd p.π ∧ D.naut.ralg p.π)

def IsRowPar (D : D7) (a : D.nd.Loc) (σ : D.what₂.FT) (Sig : List (Part D.naut.CG)) : Prop :=
  Formalism.MainNotions.N.HasParamW D.nd D.naut a σ Sig ∧ (D.nd.goodRow σ → ∀ p ∈ Sig, D.naut.csd p.π ∧ D.naut.ralg p.π)

def rowSig (D : D7) (a : D.nd.Loc) (σ : D.what₂.FT) : List (Part D.naut.CG) :=
  Classical.epsilon (IsRowPar D a σ)

theorem rowSig_isRowPar (D : D7) (hP : RowPar D) (a : D.nd.Loc) (σ : D.what₂.FT) (hσ : D.what₂.isot (D.nd.j a) σ ≠ ⊥) :
    IsRowPar D a σ (rowSig D a σ) :=
  Classical.epsilon_spec (hP a σ hσ)

theorem rowSig_spec (D : D7) (hP : RowPar D) (a : D.nd.Loc) (σ : D.what₂.FT) (hσ : D.what₂.isot (D.nd.j a) σ ≠ ⊥) :
    Formalism.MainNotions.N.HasParamW D.nd D.naut a σ (rowSig D a σ) :=
  (rowSig_isRowPar D hP a σ hσ).1

theorem rowSig_csd_ralg (D : D7) (hP : RowPar D) (a : D.nd.Loc) (σ : D.what₂.FT) (hσ : D.what₂.isot (D.nd.j a) σ ≠ ⊥)
    (hg : D.nd.goodRow σ) (π : D.naut.CG D.R.r) (hS : rowSig D a σ = [⟨D.R.r, π, 1⟩]) : D.naut.csd π ∧ D.naut.ralg π :=
  (rowSig_isRowPar D hP a σ hσ).2 hg ⟨D.R.r, π, 1⟩ (by rw [hS]; exact List.mem_singleton_self _)

def rowRho (D : D7) (hG : GalRepEx D) (a : D.nd.Loc) (π : D.naut.CG D.R.r) (hc : D.naut.csd π) (hr : D.naut.ralg π) :
    Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (Qbar (D.nd.l a)) :=
  Classical.choose (hG a D.R.r (one_le_r D) π hc hr)

theorem rowRho_spec (D : D7) (hG : GalRepEx D) (a : D.nd.Loc) (π : D.naut.CG D.R.r) (hc : D.naut.csd π)
    (hr : D.naut.ralg π) : IsRepOfSigQ D a D.R.r [⟨D.R.r, π, 1⟩] (rowRho D hG a π hc hr) :=
  Classical.choose_spec (hG a D.R.r (one_le_r D) π hc hr)

def etaChar (D : D7) (hC : ClassFieldHeckeAlgebraic D) (hη : EtaShiftInt D) (a : D.nd.Loc) : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (Qbar (D.nd.l a))ˣ :=
  Matrix.GeneralLinearGroup.det.comp (Classical.choose (hC a D.naut.etaTinv (-(D.R.t : ℝ) / 2) hη))

def rhoOfRow (D : D7) (hG : GalRepEx D) (hC : ClassFieldHeckeAlgebraic D) (hη : EtaShiftInt D) (a : D.nd.Loc)
    (π : D.naut.CG D.R.r) (hc : D.naut.csd π) (hr : D.naut.ralg π) :
    Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (Qbar (D.nd.l a)) :=
  twistRep (rowRho D hG a π hc hr) (etaChar D hC hη a)

end Formalism.L2.NR
end
end
