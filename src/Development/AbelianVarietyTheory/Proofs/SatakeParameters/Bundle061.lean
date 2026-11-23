module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle057
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle053
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle050

public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle003
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice

@[expose] public section

section

noncomputable section

namespace GlobalTheory.SplitRead

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL
  GlobalTheory.SplitWeil GlobalTheory.RowTie

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end GlobalTheory.SplitRead
end
end

section

open Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField

noncomputable section

namespace GlobalTheory.UnitaryBases

section General

variable {E : Type} [Field E] [StarRing E] {N : ℕ}

theorem stdH_eq (x y : Fin N → E) : stdH E N x y = star x ⬝ᵥ y := rfl

theorem stdH_mulVec (γ : Matrix.unitaryGroup (Fin N) E) (x y : Fin N → E) :
    stdH E N ((γ : Matrix (Fin N) (Fin N) E).mulVec x) ((γ : Matrix (Fin N) (Fin N) E).mulVec y) = stdH E N x y := by
  have h : (γ : Matrix (Fin N) (Fin N) E).conjTranspose * (γ : Matrix (Fin N) (Fin N) E) = 1 :=
    Matrix.mem_unitaryGroup_iff'.1 γ.2
  rw [stdH_eq, stdH_eq, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

theorem mulVec_surjective (γ : Matrix.unitaryGroup (Fin N) E) :
    Function.Surjective (γ : Matrix (Fin N) (Fin N) E).mulVec := by
  intro y
  have h : (γ : Matrix (Fin N) (Fin N) E) * star (γ : Matrix (Fin N) (Fin N) E) = 1 :=
    Matrix.mem_unitaryGroup_iff.1 γ.2
  exact ⟨(star (γ : Matrix (Fin N) (Fin N) E)).mulVec y, by rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]⟩

variable [NumberField E]

theorem mem_smulLat (γ : Matrix (Fin N) (Fin N) E) (L : Submodule (𝓞 E) (Fin N → E)) (y : Fin N → E) :
    y ∈ SDLat.smulLat γ L ↔ ∃ x ∈ L, γ.mulVec x = y := by
  unfold SDLat.smulLat
  rw [Submodule.mem_map]
  rfl

theorem isSDLat_smulLat (γ : Matrix.unitaryGroup (Fin N) E) {L : Submodule (𝓞 E) (Fin N → E)} (hL : IsSDLat E N L) :
    IsSDLat E N (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) E) L) := by
  obtain ⟨h1, h2, h3⟩ := hL
  refine ⟨h1.map _, ?_, fun y => ?_⟩
  · have e : (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) E) L : Set (Fin N → E)) =
        (Matrix.toLin' (γ : Matrix (Fin N) (Fin N) E)) '' (L : Set (Fin N → E)) := rfl
    rw [e, ← Submodule.map_span, h2, Submodule.map_top, LinearMap.range_eq_top]
    exact mulVec_surjective γ
  · obtain ⟨y, rfl⟩ := mulVec_surjective γ y
    constructor
    · intro hy x hx
      obtain ⟨y', hy', e⟩ := (mem_smulLat _ _ _).1 hy
      obtain ⟨x', hx', rfl⟩ := (mem_smulLat _ _ _).1 hx
      rw [← e, stdH_mulVec]
      exact (h3 y').1 hy' x' hx'
    · intro h
      refine (mem_smulLat _ _ _).2 ⟨y, (h3 y).2 fun x hx => ?_, rfl⟩
      rw [← stdH_mulVec γ]
      exact h _ ((mem_smulLat _ _ _).2 ⟨x, hx, rfl⟩)

end General

end GlobalTheory.UnitaryBases
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory

theorem bridge_degW {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (nbr : Br.NBr N)
    (i : N.Loc) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i)) :
    Br.DegW nbr i w hw := by
  have hG : IsGalois ℚ H.E := H.hostE_isGalois
  let c : H.E →+* PadicAlgCl (N.l i) := (nbr i w hw).j.comp (algebraMap H.E N.Om)
  have hK : (nbr i w hw).Kw.1 = IntermediateField.adjoin ℚ_[N.l i] (Set.range c) :=
    GlobalTheory.T.padicAlgCl_finite_dense_eq_adjoin' (N.l i) H.E c (nbr i w hw).Kw.1 (nbr i w hw).j_E (nbr i w hw).Kw.2
      (nbr i w hw).j_dense
  obtain ⟨v, hv, hc⟩ := GlobalTheory.T.exists_place_over_prime_of_padicAlgCl_embedding (N.l i) H.E c
  have h1 := GlobalTheory.T.finrank_local_field_eq_card_decomposition_group (N.l i) H.E c v hc
  have h2 := GlobalTheory.T.card_decomposition_group_eq_local_degree (N.l i) H.E v w hv hw
  have h3 : Module.finrank ℚ_[N.l i] (nbr i w hw).Kw.1 = locDeg H.E w := by
    rw [hK, h1, h2]
  exact h3

end GlobalTheory
end

section

open Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.DoubleBlock

open Matrix

variable {k Γ : Type} [Field k] [Group Γ] {a : ℕ}

theorem exists_emb (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) (hW : IsInv ρ W) :
    ∃ (σ : Γ →* GL (Fin (Module.finrank k W)) k) (φ : (Fin (Module.finrank k W) → k) ≃ₗ[k] W),
      ∀ g x, (φ ((σ g : Matrix _ _ k) *ᵥ x) : Fin a → k) = (ρ g : Matrix _ _ k) *ᵥ (φ x : Fin a → k) := by
  classical
  let φ : (Fin (Module.finrank k W) → k) ≃ₗ[k] W := (Module.finBasis k W).equivFun.symm
  let r : Γ → (W →ₗ[k] W) := fun g =>
    (Matrix.toLin' (ρ g : Matrix (Fin a) (Fin a) k)).restrict (p := W) (q := W) (fun v hv => hW g v hv)
  have hr : ∀ g v, (r g v : Fin a → k) = (ρ g : Matrix _ _ k) *ᵥ (v : Fin a → k) := fun g v => rfl
  let m : Γ →* Matrix (Fin (Module.finrank k W)) (Fin (Module.finrank k W)) k :=
    { toFun := fun g => LinearMap.toMatrix' (φ.symm.toLinearMap ∘ₗ r g ∘ₗ φ.toLinearMap)
      map_one' := by
        rw [← LinearMap.toMatrix'_id]
        congr 1
        apply LinearMap.ext
        intro x
        have : r 1 (φ x) = φ x := by
          apply Subtype.ext
          rw [hr]; simp
        simp [this]
      map_mul' := fun g h => by
        rw [← LinearMap.toMatrix'_comp]
        congr 1
        apply LinearMap.ext
        intro x
        have : r (g * h) (φ x) = r g (r h (φ x)) := by
          apply Subtype.ext
          rw [hr, hr, hr]; simp
        simp [this] }
  refine ⟨m.toHomUnits, φ, fun g x => ?_⟩
  have : ((m.toHomUnits g : Matrix _ _ k)) *ᵥ x = φ.symm (r g (φ x)) := by
    change LinearMap.toMatrix' (φ.symm.toLinearMap ∘ₗ r g ∘ₗ φ.toLinearMap) *ᵥ x = _
    rw [LinearMap.toMatrix'_mulVec]
    rfl
  rw [this, LinearEquiv.apply_symm_apply, hr]

theorem exists_emb_sum (ρ : Γ →* GL (Fin a) k) {d u : ℕ} (σ : Γ →* GL (Fin d) k)
    (τ : Γ →* GL (Fin u) k) (f₁ : (Fin d → k) →ₗ[k] (Fin a → k))
    (f₂ : (Fin u → k) →ₗ[k] (Fin a → k)) (i₁ : Function.Injective f₁) (i₂ : Function.Injective f₂)
    (h₁ : ∀ g x, f₁ ((σ g : Matrix _ _ k) *ᵥ x) = (ρ g : Matrix _ _ k) *ᵥ f₁ x)
    (h₂ : ∀ g x, f₂ ((τ g : Matrix _ _ k) *ᵥ x) = (ρ g : Matrix _ _ k) *ᵥ f₂ x)
    (hd : Disjoint (LinearMap.range f₁) (LinearMap.range f₂)) :
    ∃ f : (Fin (d + u) → k) →ₗ[k] (Fin a → k), Function.Injective f ∧
      LinearMap.range f = LinearMap.range f₁ ⊔ LinearMap.range f₂ ∧
      ∀ g x, f ((SumRepresentations.At.sumRep σ τ g : Matrix _ _ k) *ᵥ x) = (ρ g : Matrix _ _ k) *ᵥ f x := by
  let s : (Fin (d + u) → k) ≃ₗ[k] (Fin d → k) × (Fin u → k) :=
    (LinearEquiv.funCongrLeft k k finSumFinEquiv).trans (LinearEquiv.sumArrowLequivProdArrow _ _ k k)
  have hs : ∀ x, s x = (fun i => x (finSumFinEquiv (Sum.inl i)), fun i => x (finSumFinEquiv (Sum.inr i))) :=
    fun x => rfl
  refine ⟨(f₁.coprod f₂) ∘ₗ s.toLinearMap, ?_, ?_, fun g x => ?_⟩
  · have : Function.Injective (f₁.coprod f₂) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_coprod_of_disjoint_range _ _ hd,
        LinearMap.ker_eq_bot.2 i₁, LinearMap.ker_eq_bot.2 i₂, Submodule.prod_bot]
    exact this.comp s.injective
  · rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, LinearMap.range_coprod]
  · have key : s ((SumRepresentations.At.sumRep σ τ g : Matrix _ _ k) *ᵥ x) =
        ((σ g : Matrix _ _ k) *ᵥ (s x).1, (τ g : Matrix _ _ k) *ᵥ (s x).2) := by
      have hM : (SumRepresentations.At.sumRep σ τ g).val = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (σ g).val 0 0 (τ g).val) := rfl
      rw [hM, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, hs, hs]
      ext i <;> simp [Function.comp_def]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, key, LinearMap.coprod_apply, h₁, h₂,
      Matrix.mulVec_add]

theorem exists_conj (ρ : Γ →* GL (Fin a) k) {n : ℕ} (τ : Γ →* GL (Fin n) k)
    (f : (Fin n → k) →ₗ[k] (Fin a → k)) (hi : Function.Injective f) (hs : LinearMap.range f = ⊤)
    (h : ∀ g x, f ((τ g : Matrix _ _ k) *ᵥ x) = (ρ g : Matrix _ _ k) *ᵥ f x) :
    ∃ (hn : n = a) (Pm : GL (Fin a) k), ∀ g,
      ((Pm⁻¹ * ρ g * Pm : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
        Matrix.reindex (finCongr hn) (finCongr hn) ((τ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  classical
  let e := LinearEquiv.ofBijective f ⟨hi, LinearMap.range_eq_top.1 hs⟩
  have hn : n = a := by simpa using e.finrank_eq
  subst hn
  let Pm : GL (Fin n) k := ⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap,
    by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩
  have hP : ∀ x, (Pm : Matrix _ _ k) *ᵥ x = f x := fun x => LinearMap.toMatrix'_mulVec _ _
  refine ⟨rfl, Pm, fun g => ?_⟩
  have : ρ g * Pm = Pm * τ g := by
    apply Units.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    simp only [Units.val_mul, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hP, h]
  rw [mul_assoc, this, inv_mul_cancel_left]
  simp

theorem exists_conj_double : ∀ {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W₁ W₂ : Submodule k (Fin a → k)), IsSSRep ρ → IsInv ρ W₁ → IsInv ρ W₂ → W₁ ≠ ⊥ → W₁ ⊓ W₂ = ⊥ → IsoSub ρ W₁ W₂ → ∃ (d u : ℕ) (σ : Γ →* GL (Fin d) k) (υ : Γ →* GL (Fin u) k) (h : d + d + u = a) (Pm : GL (Fin a) k), 0 < d ∧ ∀ g, ((Pm⁻¹ * ρ g * Pm : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) = Matrix.reindex (finCongr h) (finCongr h) ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) k) : Matrix (Fin (d + d + u)) (Fin (d + d + u)) k) := by
  intro k Γ _ _ a ρ W₁ W₂ hss h₁ h₂ hne hdis ⟨e, he⟩
  have h12 : IsInv ρ (W₁ ⊔ W₂) := by
    intro g v hv
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
    rw [Matrix.mulVec_add]
    exact Submodule.add_mem_sup (h₁ g x hx) (h₂ g y hy)
  obtain ⟨U, hU, hc⟩ := hss _ h12
  obtain ⟨σ, φ, hφ⟩ := exists_emb ρ W₁ h₁
  obtain ⟨υ, ψ, hψ⟩ := exists_emb ρ U hU
  have r₁ : LinearMap.range (W₁.subtype ∘ₗ φ.toLinearMap) = W₁ := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  have r₂ : LinearMap.range (W₂.subtype ∘ₗ (φ.trans e).toLinearMap) = W₂ := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  have r₃ : LinearMap.range (U.subtype ∘ₗ ψ.toLinearMap) = U := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  obtain ⟨f, fi, fr, hf⟩ := exists_emb_sum ρ σ σ (W₁.subtype ∘ₗ φ.toLinearMap)
    (W₂.subtype ∘ₗ (φ.trans e).toLinearMap) (W₁.injective_subtype.comp φ.injective)
    (W₂.injective_subtype.comp (φ.trans e).injective) (fun g x => hφ g x)
    (fun g x => by
      have := he g (φ x) (h₁ g _ (φ x).2)
      have h' : φ ((σ g : Matrix _ _ k) *ᵥ x) = ⟨_, h₁ g _ (φ x).2⟩ := Subtype.ext (hφ g x)
      change (e (φ ((σ g : Matrix _ _ k) *ᵥ x)) : Fin a → k) = _
      rw [h', this]
      rfl)
    (by rw [r₁, r₂]; exact disjoint_iff.2 hdis)
  rw [r₁, r₂] at fr
  obtain ⟨F, Fi, Fr, hF⟩ := exists_emb_sum ρ (SumRepresentations.At.sumRep σ σ) υ f (U.subtype ∘ₗ ψ.toLinearMap) fi
    (U.injective_subtype.comp ψ.injective) hf (fun g x => hψ g x)
    (by rw [fr, r₃]; exact hc.disjoint)
  rw [fr, r₃, hc.sup_eq_top] at Fr
  obtain ⟨hn, Pm, hP⟩ := exists_conj ρ _ F Fi Fr hF
  exact ⟨_, _, σ, υ, hn, Pm, Nat.pos_of_ne_zero (fun h0 => hne (Submodule.finrank_eq_zero.1 h0)), hP⟩

end GlobalTheory.DoubleBlock
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AbsIrrConstituents

theorem mapRep_comp {Γ A B C : Type} [Group Γ] [CommRing A] [CommRing B] [CommRing C] {a : ℕ}
    (f : A →+* B) (g : B →+* C) (ρ : Γ →* GL (Fin a) A) :
    mapRep (g.comp f) ρ = mapRep g (mapRep f ρ) := by
  ext x i j
  rfl

theorem fixedJumps_nodup (D : D7) (i : D.nd.Loc) (P : D.naut.AV i) (τ : D.host.E →+* Qbar (D.nd.l i)) :
    (D.naut.locAutHodgeTateWeightsLevelZero i τ).Nodup := by
  have h1 := D.naut.locAut_hodgeTateWeightsLevelZero_def i τ
  rw [D.nbc.embAV_inf i P] at h1
  have h2 := (D.nbc.infW_alg _ (D.nbc.wtAU _ (D.nbc.embAV i P)) ((D.naut.iotaQC i).toRingHom.comp τ)).1
  have h3 := h2.map (f := fun z : ℂ => -z + ((D.R.nV : ℂ) - 1) / 2) (fun a b hab => by simpa using hab)
  rw [← h1] at h3
  exact h3.of_map _

end GlobalTheory.AbsIrrConstituents

namespace GlobalTheory.AbsIrrConstituents

theorem mem_of_induces' (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
    (τ : E →+* PadicAlgCl l) (w : HeightOneSpectrum (𝓞 E))
    (h : ∀ x : 𝓞 E, ‖τ (x : E)‖ < 1 ↔ x ∈ w.asIdeal) : ((l : ℕ) : 𝓞 E) ∈ w.asIdeal := by
  apply (h _).mp
  have e : τ (((l : ℕ) : 𝓞 E) : E) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by
    simp only [map_natCast]
  rw [e, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

theorem sumRep_coe {k Γ : Type} [CommRing k] [Group Γ] {a b : ℕ} (ρ : Γ →* GL (Fin a) k)
    (ρ' : Γ →* GL (Fin b) k) (g : Γ) :
    ((SumRepresentations.At.sumRep ρ ρ' g : GL (Fin (a + b)) k) : Matrix _ _ k) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (ρ g : Matrix (Fin a) (Fin a) k) 0 0 (ρ' g : Matrix (Fin b) (Fin b) k)) := rfl

theorem coe_mapRep {k L Γ : Type} [CommRing k] [CommRing L] [Group Γ] {a : ℕ} (f : k →+* L)
    (ρ : Γ →* GL (Fin a) k) (g : Γ) :
    ((mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) = (ρ g : Matrix (Fin a) (Fin a) k).map f := rfl

theorem mapRep_sumRep {k L Γ : Type} [CommRing k] [CommRing L] [Group Γ] {a b : ℕ} (f : k →+* L)
    (ρ : Γ →* GL (Fin a) k) (ρ' : Γ →* GL (Fin b) k) :
    mapRep f (SumRepresentations.At.sumRep ρ ρ') = SumRepresentations.At.sumRep (mapRep f ρ) (mapRep f ρ') := by
  ext g i j
  rw [coe_mapRep, sumRep_coe, sumRep_coe, coe_mapRep, coe_mapRep]
  simp only [Matrix.reindex_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp

theorem contQ_sumRep (D : D7) (i : D.nd.Loc) {a b : ℕ}
    (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i)))
    (ρ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin b) (Qbar (D.nd.l i)))
    (h : SumRepresentations.At.ContQ D.nd i ρ) (h' : SumRepresentations.At.ContQ D.nd i ρ') : SumRepresentations.At.ContQ D.nd i (SumRepresentations.At.sumRep ρ ρ') := by
  unfold SumRepresentations.At.ContQ at *
  simp only [sumRep_coe, Matrix.reindex_apply]
  exact (Continuous.matrix_fromBlocks h continuous_const continuous_const h').matrix_submatrix _ _

end GlobalTheory.AbsIrrConstituents

namespace GlobalTheory.AbsIrrConstituents

theorem rel_map' {k L Γ : Type} [Field k] [Field L] [Group Γ] (f : k →+* L) {a d u : ℕ} (h : d + d + u = a)
    (ρ : Γ →* GL (Fin a) k) (σ : Γ →* GL (Fin d) k) (υ : Γ →* GL (Fin u) k) (Pm : GL (Fin a) k)
    (hrel : ∀ g, ((Pm⁻¹ * ρ g * Pm : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
        Matrix.reindex (finCongr h) (finCongr h)
          ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) k) : Matrix _ _ k)) :
    ∀ g, (((Units.map (f.mapMatrix : Matrix (Fin a) (Fin a) k →+* Matrix (Fin a) (Fin a) L).toMonoidHom Pm)⁻¹ *
        mapRep f ρ g * Units.map (f.mapMatrix : Matrix (Fin a) (Fin a) k →+* Matrix (Fin a) (Fin a) L).toMonoidHom Pm :
          GL (Fin a) L) : Matrix (Fin a) (Fin a) L) =
      Matrix.reindex (finCongr h) (finCongr h)
        ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep (mapRep f σ) (mapRep f σ)) (mapRep f υ) g : GL (Fin (d + d + u)) L) :
          Matrix _ _ L) := by
  subst h
  intro g
  have e1 : (Units.map (f.mapMatrix : Matrix (Fin (d + d + u)) (Fin (d + d + u)) k →+* _).toMonoidHom Pm)⁻¹ *
      mapRep f ρ g * Units.map (f.mapMatrix : Matrix (Fin (d + d + u)) (Fin (d + d + u)) k →+* _).toMonoidHom Pm =
      Units.map (f.mapMatrix : Matrix (Fin (d + d + u)) (Fin (d + d + u)) k →+* Matrix _ _ L).toMonoidHom
        (Pm⁻¹ * ρ g * Pm) := by
    simp only [map_mul, map_inv]; rfl
  rw [e1]
  show ((Pm⁻¹ * ρ g * Pm : GL (Fin (d + d + u)) k) : Matrix (Fin (d + d + u)) (Fin (d + d + u)) k).map f = _
  rw [hrel g]
  simp only [finCongr_refl, Matrix.reindex_refl_refl]
  rw [← mapRep_sumRep, ← mapRep_sumRep, coe_mapRep]

theorem jumps_not_nodup' (D : D7) (ht : SumRepresentations.tie0 D) (i : D.nd.Loc) (τ : D.host.E →+* Qbar (D.nd.l i))
    (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (hτ : InducesW D.nd i τ w)
    (hpl : ∀ w', InducesW D.nd i τ w' → w' ∈ placesOver D.host.E (D.nd.l i))
    {a d u : ℕ} (h : d + d + u = a) (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i)))
    (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin d) (Qbar (D.nd.l i)))
    (υ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin u) (Qbar (D.nd.l i))) (Pm : GL (Fin a) (Qbar (D.nd.l i)))
    (hd : 0 < d) (hc : SumRepresentations.At.ContQ D.nd i ρ) (hcσ : SumRepresentations.At.ContQ D.nd i σ) (hcυ : SumRepresentations.At.ContQ D.nd i υ)
    (hrel : ∀ g, ((Pm⁻¹ * ρ g * Pm : GL (Fin a) (Qbar (D.nd.l i))) : Matrix (Fin a) (Fin a) (Qbar (D.nd.l i))) =
        Matrix.reindex (finCongr h) (finCongr h)
          ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) (Qbar (D.nd.l i))) :
            Matrix _ _ (Qbar (D.nd.l i))))
    (hdR : ∀ w', InducesW D.nd i τ w' → D.naut.IsdRW i ρ w') :
    ¬ (D.naut.jumpsW i ρ τ).Nodup := by
  intro hnd
  subst h
  obtain ⟨-, -, hJC, hG⟩ := ht.2.2
  obtain ⟨-, hconj, hsum, -⟩ := hG i
  have hPm : ∀ g, SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g = Pm⁻¹ * ρ g * Pm := by
    intro g; ext1; rw [hrel g]; simp only [finCongr_refl, Matrix.reindex_refl_refl]
  have hcA := contQ_sumRep D i σ σ hcσ hcσ
  obtain ⟨hdRc, -, hJc⟩ := hconj _ ρ _ hc Pm hPm
  obtain ⟨hdRs, -, hJs⟩ := hsum _ _ _ υ hcA hcυ
  obtain ⟨hdRσ, -, hJσ⟩ := hsum _ _ σ σ hcσ hcσ
  have hdR' : ∀ w', InducesW D.nd i τ w' → D.naut.IsdRW i (SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ) w' :=
    fun w' hw' => (hdRc w' (hpl w' hw')).2 (hdR w' hw')
  have hdRA : ∀ w', InducesW D.nd i τ w' → D.naut.IsdRW i (SumRepresentations.At.sumRep σ σ) w' ∧ D.naut.IsdRW i υ w' :=
    fun w' hw' => (hdRs w' (hpl w' hw')).1 (hdR' w' hw')
  have hdRσ' : ∀ w', InducesW D.nd i τ w' → D.naut.IsdRW i σ w' ∧ D.naut.IsdRW i σ w' :=
    fun w' hw' => (hdRσ w' (hpl w' hw')).1 (hdRA w' hw').1
  have e : D.naut.jumpsW i ρ τ = D.naut.jumpsW i σ τ + D.naut.jumpsW i σ τ + D.naut.jumpsW i υ τ := by
    rw [← hJc τ hdR, hJs τ hdRA, hJσ τ hdRσ']
  have hcard := hJC i _ σ w τ hw hτ (hdRσ' w hτ).1
  rw [e] at hnd
  have h2 := (Multiset.nodup_add.1 (Multiset.nodup_add.1 hnd).1).2.2
  obtain ⟨j, hj⟩ := Multiset.card_pos_iff_exists_mem.1 (hcard ▸ hd)
  exact Multiset.disjoint_left.1 h2 hj hj

end GlobalTheory.AbsIrrConstituents

namespace GlobalTheory.AbsIrrConstituents

theorem continuous_blocks' {k Γ : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [Group Γ]
    [TopologicalSpace Γ] {a b c : ℕ} (ρ : Γ →* GL (Fin a) k) (ρ₁ : Γ →* GL (Fin b) k)
    (ρ₂ : Γ →* GL (Fin c) k) (h : b + c = a) (Pm : GL (Fin a) k)
    (hrel : ∀ g, ((Pm⁻¹ * ρ g * Pm : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
      Matrix.reindex (finCongr h) (finCongr h) ((SumRepresentations.At.sumRep ρ₁ ρ₂ g : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k))
    (hc : Continuous fun g => ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)) :
    (Continuous fun g => ((ρ₁ g : GL (Fin b) k) : Matrix (Fin b) (Fin b) k)) ∧
      Continuous fun g => ((ρ₂ g : GL (Fin c) k) : Matrix (Fin c) (Fin c) k) := by
  subst h
  have hM : Continuous fun g => ((SumRepresentations.At.sumRep ρ₁ ρ₂ g : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k) := by
    have e : (fun g => ((SumRepresentations.At.sumRep ρ₁ ρ₂ g : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k)) = fun g =>
        ((Pm⁻¹ : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k) * (ρ g : Matrix _ _ k) * (Pm : Matrix _ _ k) := by
      funext g
      rw [← Units.val_mul, ← Units.val_mul, hrel g]
      simp only [finCongr_refl, Matrix.reindex_refl_refl]
    rw [e]
    exact (continuous_const.matrix_mul hc).matrix_mul continuous_const
  constructor
  · have e : (fun g => ((ρ₁ g : GL (Fin b) k) : Matrix (Fin b) (Fin b) k)) = fun g =>
        (((SumRepresentations.At.sumRep ρ₁ ρ₂ g : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k)).submatrix
          (finSumFinEquiv ∘ Sum.inl) (finSumFinEquiv ∘ Sum.inl) := by
      funext g; ext i j; simp [sumRep_coe]
    rw [e]; exact hM.matrix_submatrix _ _
  · have e : (fun g => ((ρ₂ g : GL (Fin c) k) : Matrix (Fin c) (Fin c) k)) = fun g =>
        (((SumRepresentations.At.sumRep ρ₁ ρ₂ g : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k)).submatrix
          (finSumFinEquiv ∘ Sum.inr) (finSumFinEquiv ∘ Sum.inr) := by
      funext g; ext i j; simp [sumRep_coe]
    rw [e]; exact hM.matrix_submatrix _ _

end GlobalTheory.AbsIrrConstituents

namespace GlobalTheory.AbsIrrConstituents

end GlobalTheory.AbsIrrConstituents
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.NRows

theorem point_determines : ∀ D : D7, SumRepresentations.adm1 D → SumRepresentations.adm5 D → (∀ (i : D.nd.Loc) (x : D.nd.X i), ∃ ρ, SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ) → (∀ (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa → ∀ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2) ∧ ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i ρ τ = D.naut.locAutHodgeTateWeightsLevelZero i τ) → ∀ (i : D.nd.Loc) (P P' : D.naut.AV i), D.naut.ptV i P ≠ none → D.naut.ptV i P = D.naut.ptV i P' → (∀ Pa Pa', IsBCV D.nd D.naut i P Pa → IsBCV D.nd D.naut i P' Pa' → Pa.Perm Pa') ∧ ∀ w, w ∉ D.nd.S i → w ∉ D.nd.Q i → (IsSplitPl D.host w → D.naut.locV i P w = D.naut.locV i P' w) ∧ (¬ IsSplitPl D.host w → ubc D.R.nV (D.naut.satV i P w) = ubc D.R.nV (D.naut.satV i P' w)) := by
  intro D h1 h5 hex hcomp i P P' hP hPP'
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hP
  obtain ⟨ρ, hρ⟩ := hex i x
  have hx' : D.naut.ptV i P' = some x := hPP' ▸ hx

  have key : ∀ Pa Pa', IsBCV D.nd D.naut i P Pa → IsBCV D.nd D.naut i P' Pa' →
      ∀ w, isoLoc D.nd D.naut Pa w = isoLoc D.nd D.naut Pa' w := by
    intro Pa Pa' hB hB' w
    have c := hcomp i x P Pa hx hB ρ hρ
    have c' := hcomp i x P' Pa' hx' hB' ρ hρ
    have e : D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2) =
        D.naut.lpTw (isoLoc D.nd D.naut Pa' w) ((1 - (D.R.nV : ℝ)) / 2) := by
      by_cases hw : w ∈ placesOver D.host.E (D.nd.l i)
      · rw [← (c.2 w hw).2.1, ← (c'.2 w hw).2.1]
      · rw [← c.1 w hw, ← c'.1 w hw]
    have e2 := congrArg (fun a => D.naut.lpTw a (-((1 - (D.R.nV : ℝ)) / 2))) e
    simpa only [D.naut.lpTw_add, add_neg_cancel, D.naut.lpTw_zero] using e2
  refine ⟨fun Pa Pa' hB hB' => ?_, fun w _ _ => ?_⟩
  · exact h5.2.1 Pa Pa' hB.1 hB'.1 (Filter.Eventually.of_forall (key Pa Pa' hB hB'))
  · obtain ⟨Pa, hB⟩ := h1 i P
    obtain ⟨Pa', hB'⟩ := h1 i P'
    refine ⟨fun hs => ?_, fun hs => ?_⟩
    · rw [← hB.2.2.2.1 w hs, ← hB'.2.2.2.1 w hs, key Pa Pa' hB hB' w]
    · rw [← (hB.2.2.2.2.1 w hs).2, ← (hB'.2.2.2.2.1 w hs).2, key Pa Pa' hB hB' w]

end GlobalTheory.NRows
end
