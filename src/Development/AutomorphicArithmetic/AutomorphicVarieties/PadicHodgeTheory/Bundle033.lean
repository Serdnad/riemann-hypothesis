module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle011
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle716
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle018
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmBilin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle031
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsUniqueUnramifiedCocycleFrobeniusValue
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle015
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle001

@[expose] public section

section

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

theorem UpperTheory.exists_unique_unramified_hom_of_frobenius_value :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (v : ℕ), v.Prime → ∀ (A : ValuationSubring Ω), A.valuation (v : Ω) < 1 → ∀ σ : ↥(Dec (F := ℚ) A), Formalism.ConjugateSelfDual.IsFrob (F := ℚ) A v (σ : G ℚ Ω) → ∀ (E : Type) [AddCommGroup E] [Module ℚ_[l] E] [Module.Finite ℚ_[l] E], (∀ e : E, ∃ u : ↥(Dec (F := ℚ) A) → E, QCont l u ∧ (∀ g h, u (g * h) = u g + u h) ∧ (∀ g : ↥(Dec (F := ℚ) A), (g : G ℚ Ω) ∈ Ine (F := ℚ) A → u g = 0) ∧ u σ = e) ∧ ∀ u : ↥(Dec (F := ℚ) A) → E, QCont l u → (∀ g h, u (g * h) = u g + u h) → (∀ g : ↥(Dec (F := ℚ) A), (g : G ℚ Ω) ∈ Ine (F := ℚ) A → u g = 0) → u σ = 0 → u = 0 := by
  intro Ω _ _ _ l _ v hv A hA σ hσ E _ _ _
  haveI : Fact v.Prime := ⟨hv⟩
  obtain ⟨w, hwv, hwA⟩ := GlobalTheory.DecLocal.exists_place_below (p := v) (F := ℚ) A hA
  obtain ⟨j, rfl⟩ := (UpperTheory.V.Loc.decEmb (F := ℚ) (Ω := Ω) (v := v)).1 _ w hwA hwv
  obtain ⟨hemb, hrange, hcomap, -, -, -, hfrob⟩ := UpperTheory.V.Loc.iotaFacts (v := v) j
  letI : TopologicalSpace E := moduleTopology ℚ_[l] E
  haveI : IsModuleTopology ℚ_[l] E := ⟨rfl⟩
  haveI : IsTopologicalAddGroup E := IsModuleTopology.topologicalAddGroup ℚ_[l] E
  let ρ : Representation ℚ_[l] (Formalism.BasicNotions.Loc.GQ v) E := Representation.trivial ℚ_[l] _ E
  have hρ : ∀ g x, ρ g x = x := fun _ _ => rfl
  have hcont : ContAction ρ := by
    show Continuous fun p : Formalism.BasicNotions.Loc.GQ v × E => ρ p.1 p.2
    simp only [hρ]
    exact continuous_snd
  have hI : ∀ g ∈ Iq v, ρ g = 1 := fun _ _ => rfl
  have hmem : ∀ c : Formalism.BasicNotions.Loc.GQ v → E,
      c ∈ Z1 ρ ↔ Continuous c ∧ ∀ g h, c (g * h) = c g + c h := by
    intro c
    exact Iff.rfl
  have hsurj : ∀ g : ↥(Dec (F := ℚ) (placeJ j)), ∃ x, iota j x = (g : G ℚ Ω) := by
    intro g
    have hg : (g : G ℚ Ω) ∈ (iota j).range := by
      rw [hrange]
      exact g.2
    exact hg
  choose inv hinv using hsurj
  have hinj : Function.Injective (iota j) := hemb.injective
  have hinv_mul : ∀ g h, inv (g * h) = inv g * inv h := by
    intro g h
    apply hinj
    rw [map_mul, hinv, hinv, hinv]
    rfl
  have hinv_cont : Continuous inv := by
    rw [hemb.isInducing.continuous_iff]
    have hfun : (iota j ∘ inv) = fun g : ↥(Dec (F := ℚ) (placeJ j)) => (g : G ℚ Ω) := funext hinv
    rw [hfun]
    exact continuous_subtype_val
  have hmemr : ∀ x, iota j x ∈ Dec (F := ℚ) (placeJ j) := by
    intro x
    rw [← hrange]
    exact ⟨x, rfl⟩
  let ψ : Formalism.BasicNotions.Loc.GQ v → ↥(Dec (F := ℚ) (placeJ j)) := fun x => ⟨iota j x, hmemr x⟩
  have hψ_cont : Continuous ψ := hemb.continuous.subtype_mk _
  have hψ_mul : ∀ x y, ψ (x * y) = ψ x * ψ y := by
    intro x y
    apply Subtype.ext
    simp [ψ]
  have hψinv : ∀ g, ψ (inv g) = g := fun g => Subtype.ext (hinv g)
  obtain ⟨τ, hτ⟩ : (σ : G ℚ Ω) ∈ (iota j).range := by
    rw [hrange]
    exact σ.2
  have hτF : UpperTheory.V.Loc.IsFrob τ := (hfrob τ).2 (hτ ▸ hσ)
  have hinvσ : inv σ = τ := hinj (by rw [hinv, hτ])
  have hIq : ∀ x, x ∈ Iq v ↔ iota j x ∈ Ine (F := ℚ) (placeJ j) := by
    intro x
    rw [← hcomap]
    rfl
  refine ⟨?_, ?_⟩
  · intro e
    obtain ⟨c, ⟨hcZ, hcI, hcσ⟩, -⟩ := UpperTheory.V.Loc.existsUnique_unramified_cocycle_frobenius_value (l := l) (A := ℚ_[l]) ρ hcont hI τ hτF e
    obtain ⟨hcc, hcm⟩ := (hmem c).1 hcZ
    refine ⟨fun g => c (inv g), ?_, ?_, ?_, ?_⟩
    · exact hcc.comp hinv_cont
    · intro g h
      simp only [hinv_mul, hcm]
    · intro g hg
      apply hcI
      rw [hIq, hinv]
      exact hg
    · simp only [hinvσ, hcσ]
  · intro u hu hum huI huσ
    obtain ⟨c0, -, huniq⟩ := UpperTheory.V.Loc.existsUnique_unramified_cocycle_frobenius_value (l := l) (A := ℚ_[l]) ρ hcont hI τ hτF 0
    have hc : (fun x => u (ψ x)) = 0 := by
      have h1 : (fun x => u (ψ x)) = c0 := by
        apply huniq
        refine ⟨(hmem _).2 ⟨hu.comp hψ_cont, ?_⟩, ?_, ?_⟩
        · intro g h
          simp only [hψ_mul, hum]
        · intro g hg
          exact huI _ ((hIq g).1 hg)
        · have : ψ τ = σ := Subtype.ext hτ
          simp only [this, huσ]
      have h2 : (0 : Formalism.BasicNotions.Loc.GQ v → E) = c0 := by
        apply huniq
        refine ⟨(hmem _).2 ⟨continuous_const, ?_⟩, ?_, ?_⟩
        · intro g h
          simp
        · intro g _
          rfl
        · rfl
      rw [h1, h2]
    funext g
    have := congrFun hc (inv g)
    simp only [hψinv] at this
    exact this
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial
open Topology

section SlopeTestRemainingChoices

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B]
  [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B]

omit [IsTopologicalGroup G] in
private theorem cont_ch (κ : G →* Bˣ) (h : Continuous fun g => (κ g : B)) : ContAction (chRep κ) := by
  unfold ReciprocityTheory.Gal.ContAction
  exact (h.comp continuous_fst).mul continuous_snd

omit [IsTopologicalGroup G] in
private theorem cont_col (r : G →* GL (Fin 3) B) (h : ∀ a b, Continuous fun g => (r g : Matrix (Fin 3) (Fin 3) B) a b) :
    ContAction (colRep r) := by
  unfold ReciprocityTheory.Gal.ContAction
  refine continuous_pi fun a => ?_
  change Continuous fun p : G × (Fin 3 → B) => ∑ b, (r p.1 : Matrix (Fin 3) (Fin 3) B) a b * p.2 b
  exact continuous_finsetSum _ fun b _ => ((h a b).comp continuous_fst).mul ((continuous_apply b).comp continuous_snd)

private theorem cr_div (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) (α β γ : G →* Bˣ)
    (hα : Continuous fun g => (α g : B)) (hβ : Continuous fun g => (β g : B)) (hγ : Continuous fun g => (γ g : B))
    (h : ∀ g, γ g * α g = β g) (ha : IsCr φ (chRep α)) (hb : IsCr φ (chRep β)) : IsCr φ (chRep γ) := by
  refine (isCrys_isDR_internalHom φ hφ (chRep α) (chRep β) (chRep γ) (cont_ch α hα) (cont_ch β hβ) (cont_ch γ hγ)
    (LinearMap.mul ℚ_[l] B) (fun g w x => ?_) (fun w w' hw => ?_)).1 ha hb
  · change ((γ g : B) * w) * ((α g : B) * x) = (β g : B) * (w * x)
    rw [← h g, Units.val_mul]
    ring
  · simpa using congrArg (fun f : B →ₗ[ℚ_[l]] B => f 1) hw

private theorem cr_diag (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) (r : G →* GL (Fin 3) B) (κ : Fin 3 → G →* Bˣ)
    (ht : UpperTri r κ) (hc : ∀ a b, Continuous fun g => (r g : Matrix (Fin 3) (Fin 3) B) a b)
    (hr : IsCr φ (colRep r)) (a : Fin 3) : IsCr φ (chRep (κ a)) := by
  have hκ : ∀ a, Continuous fun g => (κ a g : B) := fun a => by
    simpa only [fun g => (ht g).2 a] using hc a a
  have hap : ∀ g x a, colRep r g x a = ∑ b, (r g : Matrix (Fin 3) (Fin 3) B) a b * x b := fun g x a => rfl
  have h10 := fun g => (ht g).1 1 0 (by decide)
  have h20 := fun g => (ht g).1 2 0 (by decide)
  have h21 := fun g => (ht g).1 2 1 (by decide)
  have hch : ∀ (χ : G →* Bˣ) g x, chRep χ g x = (χ g : B) * x := fun _ _ _ => rfl
  have c0 : IsCr φ (chRep (κ 0)) := by
    refine ((isCrys_isDR_sub_quot φ hφ (chRep (κ 0)) (colRep r) (cont_ch _ (hκ 0)) (cont_col r hc)
      (LinearMap.single ℚ_[l] (fun _ : Fin 3 => B) 0) fun g x => ?_).1 (fun x y h => by simpa using congrFun h 0)).1 hr
    funext a
    rw [hap, hch, Fin.sum_univ_three]
    fin_cases a <;> simp [h10, h20, (ht g).2]
  have c2 : IsCr φ (chRep (κ 2)) := by
    refine ((isCrys_isDR_sub_quot φ hφ (colRep r) (chRep (κ 2)) (cont_col r hc) (cont_ch _ (hκ 2))
      (LinearMap.proj 2) fun g x => ?_).2 (fun y => ⟨fun _ => y, rfl⟩)).1 hr
    rw [LinearMap.proj_apply, LinearMap.proj_apply, hap, hch, Fin.sum_univ_three, h20, h21, (ht g).2]
    ring
  have h12 : Continuous fun g => ((κ 1 * κ 2) g : B) := (hκ 1).mul (hκ 2)
  have c12 : IsCr φ (chRep (κ 1 * κ 2)) := by
    refine (admissible_of_bilinear_openSubgroup_galois φ hφ (colRep r) (colRep r) (chRep (κ 1 * κ 2)) (cont_col r hc) (cont_col r hc) (cont_ch _ h12)
      (LinearMap.mk₂ ℚ_[l] (fun x y : Fin 3 → B => x 1 * y 2 - x 2 * y 1) ?_ ?_ ?_ ?_) (fun g x y => ?_) ?_).1 hr hr
    · intro x x' y; simp only [Pi.add_apply]; ring
    · intro c x y; simp only [Pi.smul_apply, smul_mul_assoc, smul_sub]
    · intro x y y'; simp only [Pi.add_apply]; ring
    · intro c x y; simp only [Pi.smul_apply, mul_smul_comm, smul_sub]
    · simp only [LinearMap.mk₂_apply, hap, hch, Fin.sum_univ_three, h10, h20, h21, (ht g).2, MonoidHom.mul_apply,
        Units.val_mul]
      ring
    · refine eq_top_iff.2 fun y _ => Submodule.subset_span ⟨(Pi.single 1 y, Pi.single 2 1), ?_⟩
      simp
  fin_cases a
  · exact c0
  · exact cr_div φ hφ (κ 2) (κ 1 * κ 2) (κ 1) (hκ 2) h12 (hκ 1) (fun g => rfl) c2 c12
  · exact c2

end SlopeTestRemainingChoices

private theorem cr_transport {l : ℕ} [Fact l.Prime] {G G' A V : Type} [Group G] [Group G'] [CommRing A]
    [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V]
    (φ : G →* GQ l) (ρ : Representation A G V) (φ' : G' →* GQ l) (ρ' : Representation A G' V)
    (e : G' → G) (he : Function.Surjective e) (h1 : ∀ g, φ' g = φ (e g)) (h2 : ∀ g, ρ' g = ρ (e g))
    (h : IsCr φ ρ) : IsCr φ' ρ' := by
  have h3 : Dcr φ' (resCoef ℚ_[l] ρ') = Dcr φ (resCoef ℚ_[l] ρ) := by
    unfold Dcr
    refine he.iInf_congr _ fun g => ?_
    unfold actC
    rw [h1]
    change _ = LinearMap.ker (TensorProduct.AlgebraTensorModule.map ((ρ' g).restrictScalars ℚ_[l]) _ - _)
    rw [h2]
    rfl
  have h4 : φ'.range = φ.range := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨e g, (h1 g).symm⟩
    · rintro ⟨g, rfl⟩
      obtain ⟨g, rfl⟩ := he g
      exact ⟨g, h1 g⟩
  unfold IsCr at h ⊢
  rw [h3, h4, h]

theorem UpperTheory.V.Loc.triDiag :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (u : GQ l →* GG (m := 3) (R := B)), Dat3.InDtri D (π : B →+* E) u → ∀ s ∈ Iq l, ∀ a, (u s).mat a a = algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s) := by
  intro l _ O _ _ _ _ _ _ _ D E _ _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ u hu s hs a
  letI : TopologicalSpace B := moduleTopology ℚ_[l] B
  haveI : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
  haveI : IsTopologicalRing B := IsModuleTopology.isTopologicalRing ℚ_[l] B
  have hG : IsOpen (D.η.ker : Set (GQ l)) := by
    have : D.η.ker = GK D.Kv := Subgroup.ext fun g => D.η_ker g
    rw [this]
    have := D.Kv.2
    exact IntermediateField.fixingSubgroup_isOpen D.Kv.1
  have hφ : IsOpenEmbedding D.η.ker.subtype := hG.isOpenEmbedding_subtypeVal
  let H : Subgroup ↥D.η.ker := D.HL.subgroupOf D.η.ker
  have hH : IsOpen (H : Set ↥D.η.ker) := (hG.inter D.τ_open).preimage continuous_subtype_val
  have hφH : IsOpenEmbedding (D.η.ker.subtype.comp H.subtype) := hφ.comp hH.isOpenEmbedding_subtypeVal
  let r : ↥D.η.ker →* GL (Fin 3) B := glPart D.η u hu.mult
  have hr : ∀ g a b, (r g : Matrix (Fin 3) (Fin 3) B) a b = (u g).mat a b := fun _ _ _ => rfl
  have hlow : ∀ g (a b : Fin 3), b < a → (r g : Matrix (Fin 3) (Fin 3) B) a b = 0 := fun g a b h =>
    hu.tri g a b (by
      have : (b : ℕ) < a := h
      simp only [wt, wt1]
      omega)
  let k : Fin 3 → ↥D.η.ker →* B := fun a =>
    { toFun := fun g => (r g : Matrix (Fin 3) (Fin 3) B) a a
      map_one' := by simp
      map_mul' := fun g h => by
        rw [map_mul, Units.val_mul, Matrix.mul_apply]
        refine Finset.sum_eq_single a (fun b _ hb => ?_) (by simp)
        rcases lt_or_gt_of_ne hb with h' | h'
        · rw [hlow g a b h', zero_mul]
        · rw [hlow h b a h', mul_zero] }
  let κ : Fin 3 → ↥D.η.ker →* Bˣ := fun a => (k a).toHomUnits
  have hκ : ∀ a g, (κ a g : B) = (u g).mat a a := fun _ _ => rfl
  have hc : ∀ a b, Continuous fun g => (r g : Matrix (Fin 3) (Fin 3) B) a b := fun a b =>
    Continuous.comp (hu.cont a b) continuous_subtype_val
  have hcκ : Continuous fun g => (κ a g : B) := hc a a
  let σ : B →ₐ[ℚ_[l]] B := (IsScalarTower.toAlgHom ℚ_[l] E B).comp (π.restrictScalars ℚ_[l])
  have hσ : Continuous σ := IsModuleTopology.continuous_of_linearMap σ.toLinearMap
  let ψ : ↥D.η.ker →* Bˣ := (Units.map (σ : B →* B)).comp (κ a)
  have hψ0 : ∀ g, (ψ g : B) = algebraMap E B (π (κ a g)) := fun _ => rfl
  have hψ : ∀ g, ψ g = Units.map (algebraMap O B : O →* B) (D.Ψ g ^ wt1 a) := fun g => by
    have h1 : (GG.map (π : B →+* E) (u g)).mat a a = (D.rz E g).mat a a := by
      rw [← hu.red]; rfl
    have h2 : (D.rz E g).mat a a = algebraMap O E ((D.Ψ g ^ wt1 a : Oˣ) : O) := by
      change algebraMap O E ((tor O (D.Ψ g) : Matrix (Fin 3) (Fin 3) O) a a) = _
      rw [tor_val, Matrix.diagonal_apply_eq]
    apply Units.ext
    rw [hψ0, hκ]
    change algebraMap E B ((GG.map (π : B →+* E) (u g)).mat a a) = algebraMap O B _
    rw [h1, h2, ← IsScalarTower.algebraMap_apply]
  have hcψ : Continuous fun g => (ψ g : B) := hσ.comp hcκ
  have hcq : Continuous fun g => ((κ a * ψ⁻¹) g : B) := by
    have : (fun g => ((κ a * ψ⁻¹) g : B)) = fun g => (κ a g : B) * (ψ g⁻¹ : B) := by
      funext g
      simp
    rw [this]
    exact hcκ.mul (hcψ.comp continuous_inv)
  obtain ⟨ρ, hρ, hcr⟩ := hu.cr
  have c1 : IsCr (D.η.ker.subtype.comp H.subtype) (colRep (r.comp H.subtype)) := by
    refine cr_transport _ _ _ _ (fun g => (⟨g.1.1, g.2⟩ : ↥D.HL)) (fun g => ⟨⟨⟨g.1, g.2.1⟩, g.2⟩, rfl⟩)
      (fun _ => rfl) (fun g => ?_) hcr
    change Matrix.toLin' _ = Matrix.toLin' _
    rw [hρ]
    rfl
  have c2 : IsCr (D.η.ker.subtype.comp H.subtype) (chRep ((κ a).comp H.subtype)) :=
    cr_diag _ hφH (r.comp H.subtype) (fun a => (κ a).comp H.subtype) (fun g => ⟨hlow g, fun _ => rfl⟩)
      (fun a b => (hc a b).comp continuous_subtype_val) c1 a
  have c3 : IsCr (D.η.ker.subtype.comp H.subtype) (chRep (ψ.comp H.subtype)) := by
    refine crUnr _ hφH _ (cont_ch _ (hcψ.comp continuous_subtype_val)) (D.e * wt1 a) fun g hg x => ?_
    have hτ : D.τ g = 1 := g.2.2
    have h1 : Units.map (algebraMap O B : O →* B) (cycA l l O g) = cycA l l B g := by
      apply Units.ext
      exact (IsScalarTower.algebraMap_apply ℤ_[l] O B _).symm
    have h2 : ψ g = cycA l l B g ^ ((D.e : ℤ) * wt1 a) := by
      rw [hψ, D.Ψ_I g.1.1 hg, hτ, mul_one, map_zpow, map_pow, h1, zpow_mul, zpow_natCast]
    change (ψ g : B) • x = _
    rw [h2]
    rfl
  have c4 : IsCr (D.η.ker.subtype.comp H.subtype) (chRep ((κ a * ψ⁻¹).comp H.subtype)) :=
    cr_div _ hφH _ _ _ (hcψ.comp continuous_subtype_val) (hcκ.comp continuous_subtype_val)
      (hcq.comp continuous_subtype_val) (fun g => by simp) c3 c2
  have key := crUnipChar D.η.ker.subtype hφ (κ a * ψ⁻¹) hcq (fun g => hπ _ (by
      have h1 : ((κ a * ψ⁻¹) g : B) - 1 = ((κ a g : B) - ψ g) * (((ψ g)⁻¹ : Bˣ) : B) := by
        simp [sub_mul]
      rw [h1, map_mul, map_sub, hψ0, AlgHom.commutes]
      simp)) H hH c4 ⟨s, D.η_unr s hs⟩ hs
  have h5 : κ a ⟨s, D.η_unr s hs⟩ = ψ ⟨s, D.η_unr s hs⟩ := by
    simpa [mul_inv_eq_one] using key
  refine (hκ a ⟨s, D.η_unr s hs⟩).symm.trans ?_
  rw [h5, hψ]
  rfl
end
