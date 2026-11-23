module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle026
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteLevelCyclotomicOfOpenEmbedding
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle022
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Mathlib.Algebra.DualNumber
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmBilin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MatrixExtendByZeroApply
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Instances.TrivSqZeroExt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc Topology NumberField IsDedekindDomain

private theorem bkAbove_avg {k G W : Type} [Field k] [CharZero k] [Group G] [AddCommGroup W] [Module k W]
    (a : G → W →ₗ[k] W) (hmul : ∀ g h w, a (g * h) w = a g (a h w)) (f : G → W)
    (hf : ∀ g h, f (g * h) = f g + a g (f h)) (H : Subgroup G) [H.FiniteIndex] (x : W)
    (hx : ∀ h ∈ H, f h = a h x - x) : ∃ y, ∀ g, f g = a g y - y := by
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  set f' : G → W := fun g => f g - (a g x - x) with hf'
  have hc : ∀ g h, f' (g * h) = f' g + a g (f' h) := by
    intro g h
    simp only [hf', hf, hmul, map_sub]
    abel
  have hH : ∀ g h, h ∈ H → f' (g * h) = f' g := by
    intro g h hh
    rw [hc]
    have : f' h = 0 := by simp only [hf', hx h hh, sub_self]
    rw [this, map_zero, add_zero]
  let F : G ⧸ H → W := Quotient.lift f' (by
    intro g g' hgg
    have h1 : g⁻¹ * g' ∈ H := QuotientGroup.leftRel_apply.1 hgg
    have := hH g _ h1
    rw [mul_inv_cancel_left] at this
    exact this.symm)
  have hF : ∀ (g : G) (q : G ⧸ H), F (g • q) = f' g + a g (F q) := by
    intro g q
    induction q using QuotientGroup.induction_on with
    | H z => exact hc g z
  set S : W := ∑ q, F q with hS
  have hsum : ∀ g, S = (Fintype.card (G ⧸ H) : k) • f' g + a g S := by
    intro g
    have e1 : ∑ q, F (g • q) = S := Equiv.sum_comp (MulAction.toPerm g) F
    refine e1.symm.trans ?_

    simp only [hF, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← map_sum,
    Nat.cast_smul_eq_nsmul, ← hS]
  have hn : (Fintype.card (G ⧸ H) : k) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨x - (Fintype.card (G ⧸ H) : k)⁻¹ • S, fun g => ?_⟩
  have e : f' g = (Fintype.card (G ⧸ H) : k)⁻¹ • (S - a g S) := by
    rw [eq_inv_smul_iff₀ hn, eq_sub_iff_add_eq]
    exact (hsum g).symm
  have e2 : f g = f' g + (a g x - x) := by simp only [hf', sub_add_cancel]
  rw [e2, e, map_sub, map_smul, smul_sub]
  abel

theorem UpperTheory.V.Loc.bkAbove :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (j : Ω →+* Om l) {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (φ : H →* GQ l) (ψ : H →* G F Ω), IsOpenEmbedding φ → (∀ h y, φ h (j y) = j (ψ h y)) → ∀ {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V] (ρ : Representation C (G F Ω) V), ∀ c ∈ Z1 ρ, ((fun h => c (ψ h)) ∈ finiteCocycles φ (ρ.comp ψ) ↔ (fun x : ↥(UpperTheory.V.Af.decJ F j) => c x.1.1) ∈ finiteCocycles ((MonoidHom.snd _ _).comp (UpperTheory.V.Af.decJ F j).subtype) (ρ.comp ((MonoidHom.fst _ _).comp (UpperTheory.V.Af.decJ F j).subtype))) := by
  intro F Ω _ _ _ _ _ _ l _ j H _ _ _ φ ψ hφ hj C V _ _ _ _ _ _ _ _ _ ρ c hc
  let θ : H →* ↥(UpperTheory.V.Af.decJ F j) := (ψ.prod φ).codRestrict _ (fun h y => hj h y)
  let s : ↥(UpperTheory.V.Af.decJ F j) →* GQ l := (MonoidHom.snd _ _).comp (UpperTheory.V.Af.decJ F j).subtype
  let p : ↥(UpperTheory.V.Af.decJ F j) →* G F Ω := (MonoidHom.fst _ _).comp (UpperTheory.V.Af.decJ F j).subtype
  have hs : IsOpenEmbedding s := (UpperTheory.V.Loc.decJFacts (F := F) j).1
  have hθ : Continuous θ := hs.isEmbedding.continuous_iff.2 hφ.continuous
  have hp : Continuous p := continuous_fst.comp continuous_subtype_val
  have hψ : Continuous ψ := hp.comp hθ
  constructor
  · rintro ⟨-, x, hx⟩
    refine ⟨⟨hc.1.comp hp, fun g h => hc.2 _ _⟩, ?_⟩
    haveI : CompactSpace (GQ l) := inferInstanceAs (CompactSpace (Om l ≃ₐ[ℚ_[l]] Om l))
    haveI : Finite (GQ l ⧸ φ.range) := Subgroup.quotient_finite_of_isOpen _ hφ.isOpen_range
    haveI : φ.range.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    haveI : (φ.range.comap s).FiniteIndex := ⟨by
      rw [Subgroup.index_comap]
      exact Subgroup.FiniteIndex.index_ne_zero⟩
    refine bkAbove_avg (k := ℚ_[l]) (fun g => (actC s (ρ.comp p) g).restrictScalars ℚ_[l]) ?_
      (fun g => c (p g) ⊗ₜ[ℚ_[l]] (1 : Bcr l)) ?_ (φ.range.comap s) x ?_
    · intro g h w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [actC]
      | add u v hu hv => simp only [map_add (f := _), hu, hv]
    · intro g h
      simp [actC, hc.2 (p g) (p h), TensorProduct.add_tmul]
    · rintro g ⟨h, hh⟩
      obtain rfl : θ h = g := hs.injective hh
      exact hx h
  · rintro ⟨-, x, hx⟩
    exact ⟨⟨hc.1.comp hψ, fun g h => (congrArg c (map_mul ψ g h)).trans (hc.2 _ _)⟩, x, fun h => hx (θ h)⟩
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc.DeformationPairing

private def extRep {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]
    (ρ : Representation A G V) (c : G → V) (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) :
    Representation A G (V × A) where
  toFun g := ((ρ g).comp (LinearMap.fst A V A) + (LinearMap.snd A V A).smulRight (c g)).prod (LinearMap.snd A V A)
  map_one' := by
    have h1 : c 1 = 0 := by simpa using hc 1 1
    refine LinearMap.ext fun x => ?_
    simp [h1]
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    simp [hc, add_assoc, add_comm, add_left_comm]

private theorem extRep_apply {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]
    (ρ : Representation A G V) (c : G → V) (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) (g : G) (x : V × A) :
    extRep ρ c hc g x = (ρ g x.1 + x.2 • c g, x.2) := rfl

private theorem contAction_sub {G A V : Type} [Group G] [TopologicalSpace G] [CommRing A] [AddCommGroup V]
    [Module A V] [TopologicalSpace V] (ρ : Representation A G V) (h : ContAction ρ) (H : Subgroup G) :
    ContAction (ρ.comp H.subtype : Representation A H V) :=
  h.comp (f := fun p : H × V => ((p.1 : G), p.2))
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

private noncomputable def pair (Q : Type) {E : Type} [Field Q] [Field E] [Algebra Q E] (n : ℕ) :
    (Matrix (Fin n) (Fin n) E × E) →ₗ[Q] (Fin n → E) →ₗ[Q] (Fin n → DualNumber E) :=
  LinearMap.mk₂ Q (fun w v i => (⟨w.2 * v i, (w.1.mulVec v) i⟩ : DualNumber E))
    (fun w w' v => by
      funext i; refine TrivSqZeroExt.ext ?_ ?_ <;> simp [add_mul, Matrix.add_mulVec] <;> rfl)
    (fun c w v => by
      funext i; refine TrivSqZeroExt.ext ?_ ?_ <;> simp [Matrix.smul_mulVec] <;> rfl)
    (fun w v v' => by
      funext i; refine TrivSqZeroExt.ext ?_ ?_ <;> simp [mul_add, Matrix.mulVec_add] <;> rfl)
    (fun c w v => by
      funext i; refine TrivSqZeroExt.ext ?_ ?_ <;> simp [Matrix.mulVec_smul] <;> rfl)

private theorem pair_fst (Q : Type) {E : Type} [Field Q] [Field E] [Algebra Q E] (n : ℕ)
    (w : Matrix (Fin n) (Fin n) E × E) (v : Fin n → E) (i : Fin n) : (pair Q n w v i).fst = w.2 * v i := rfl

private theorem pair_snd (Q : Type) {E : Type} [Field Q] [Field E] [Algebra Q E] (n : ℕ)
    (w : Matrix (Fin n) (Fin n) E × E) (v : Fin n → E) (i : Fin n) :
    (pair Q n w v i).snd = (w.1.mulVec v) i := rfl

private theorem mulVec_fst {E : Type} [Field E] {n : ℕ} (R S : Matrix (Fin n) (Fin n) E)
    (R' : Matrix (Fin n) (Fin n) (DualNumber E)) (h : ∀ i j, R' i j = ⟨R i j, S i j⟩)
    (w : Fin n → DualNumber E) (i : Fin n) :
    (R'.mulVec w i).fst = R.mulVec (fun j => (w j).fst) i := by
  have h1 : ∀ i j, (R' i j).fst = R i j := fun i j => by rw [h]; rfl
  simp [Matrix.mulVec, dotProduct, TrivSqZeroExt.fst_sum, h1]

private theorem mulVec_snd {E : Type} [Field E] {n : ℕ} (R S : Matrix (Fin n) (Fin n) E)
    (R' : Matrix (Fin n) (Fin n) (DualNumber E)) (h : ∀ i j, R' i j = ⟨R i j, S i j⟩)
    (w : Fin n → DualNumber E) (i : Fin n) :
    (R'.mulVec w i).snd = R.mulVec (fun j => (w j).snd) i + S.mulVec (fun j => (w j).fst) i := by
  have h1 : ∀ i j, (R' i j).fst = R i j := fun i j => by rw [h]; rfl
  have h2 : ∀ i j, (R' i j).snd = S i j := fun i j => by rw [h]; rfl
  simp [Matrix.mulVec, dotProduct, TrivSqZeroExt.snd_sum, h1, h2, Finset.sum_add_distrib]

private theorem ad_mulVec {G E : Type} [Group G] [Field E] {n : ℕ} (r : G →* GL (Fin n) E) (g : G)
    (X : Matrix (Fin n) (Fin n) E) (v : Fin n → E) :
    (adGL r g X).mulVec (colRep r g v) = colRep r g (X.mulVec v) := by
  change ((r g : Matrix (Fin n) (Fin n) E) * X * ((r g)⁻¹ : GL (Fin n) E)).mulVec
    (Matrix.toLin' (r g : Matrix (Fin n) (Fin n) E) v) = Matrix.toLin' (r g : Matrix (Fin n) (Fin n) E) _
  simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

end UpperTheory.V.Loc.DeformationPairing

open UpperTheory.V.Loc.DeformationPairing in
theorem UpperTheory.V.Loc.deformCr :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E] {n : ℕ} (r : G →* GL (Fin n) E), Continuous (fun g => (r g : Matrix (Fin n) (Fin n) E)) → ∀ y ∈ Z1 (adGL r), ∀ r' : G →* GL (Fin n) (DualNumber E), (∀ g i j, (r' g : Matrix (Fin n) (Fin n) (DualNumber E)) i j = ⟨(r g : Matrix (Fin n) (Fin n) E) i j, (y g * (r g : Matrix (Fin n) (Fin n) E)) i j⟩) → ∀ (H : Subgroup G) [H.Normal], IsOpen (H : Set G) → (CrOn φ (colRep r') H ↔ CrOn φ (colRep r) H ∧ y ∈ UpperTheory.V.Loc.finiteCocycles φ (adGL r)) := by
  intro l _ G _ _ _ φ hφ E _ _ _ _ _ _ n r hr y hy r' hr' H _ hH
  haveI : IsModuleTopology ℚ_[l] (DualNumber E) := inferInstanceAs (IsModuleTopology ℚ_[l] (E × E))
  haveI : FiniteDimensional ℚ_[l] (DualNumber E) := inferInstanceAs (FiniteDimensional ℚ_[l] (E × E))
  haveI : IsModuleTopology ℚ_[l] (Matrix (Fin n) (Fin n) E) :=
    inferInstanceAs (IsModuleTopology ℚ_[l] (Fin n → Fin n → E))
  have hψ : IsOpenEmbedding (φ.comp H.subtype) := hφ.comp hH.isOpenEmbedding_subtypeVal
  have cV : ContAction (colRep r) :=
    Continuous.matrix_mulVec (hr.comp continuous_fst) continuous_snd
  have hr'c : Continuous (fun g => (r' g : Matrix (Fin n) (Fin n) (DualNumber E))) := by
    refine continuous_matrix fun i j => ?_
    simp only [hr']
    exact (hr.matrix_elem i j).prodMk ((hy.1.matrix_mul hr).matrix_elem i j)
  have cW : ContAction (colRep r') :=
    Continuous.matrix_mulVec (hr'c.comp continuous_fst) continuous_snd
  have cM : ContAction (adGL r) := by
    have hi : Continuous (fun g => (((r g)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) := by
      simp only [← map_inv]
      exact hr.comp continuous_inv
    exact ((hr.comp continuous_fst).matrix_mul continuous_snd).matrix_mul (hi.comp continuous_fst)
  have cH : ContAction (extRep (adGL r) y hy.2) := by
    unfold ReciprocityTheory.Gal.ContAction
    simp only [extRep_apply]
    refine Continuous.prodMk (Continuous.add ?_ ?_) (continuous_snd.comp continuous_snd)
    · exact Continuous.comp (f := fun p : G × (Matrix (Fin n) (Fin n) E × E) => (p.1, p.2.1)) cM (by fun_prop)
    · exact (continuous_snd.comp continuous_snd).smul (hy.1.comp continuous_fst)
  have hb : ∀ g w v, pair ℚ_[l] n (extRep (adGL r) y hy.2 g w) (colRep r g v)
      = colRep r' g (pair ℚ_[l] n w v) := by
    intro g w v
    funext i
    have e' : colRep r' g (pair ℚ_[l] n w v)
      = (r' g : Matrix (Fin n) (Fin n) (DualNumber E)).mulVec (pair ℚ_[l] n w v) := rfl
    have e : ∀ u, colRep r g u = (r g : Matrix (Fin n) (Fin n) E).mulVec u := fun _ => rfl
    have e1 : (fun j => (pair ℚ_[l] n w v j).fst) = w.2 • v := rfl
    have e2 : (fun j => (pair ℚ_[l] n w v j).snd) = w.1.mulVec v := rfl
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [e', mulVec_fst _ _ _ (hr' g), e1, pair_fst, extRep_apply, Matrix.mulVec_smul, e]; rfl
    · rw [e', mulVec_snd _ _ _ (hr' g), e1, e2, pair_snd, extRep_apply, Matrix.add_mulVec, ad_mulVec, e, e,
        Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      rfl
  have crM : CrOn φ (colRep r) H → CrOn φ (adGL r) H := fun h =>
    (isCrys_isDR_internalHom (φ.comp H.subtype) hψ _ _ _ (contAction_sub _ cV H) (contAction_sub _ cV H) (contAction_sub _ cM H)
      (LinearMap.mk₂ ℚ_[l] (fun (X : Matrix (Fin n) (Fin n) E) (v : Fin n → E) => X.mulVec v)
        (fun _ _ _ => Matrix.add_mulVec _ _ _) (fun _ _ _ => Matrix.smul_mulVec _ _ _)
        (fun _ _ _ => Matrix.mulVec_add _ _ _) (fun _ _ _ => Matrix.mulVec_smul _ _ _))
      (fun g X v => ad_mulVec r g X v)
      (fun X Y hXY => Matrix.ext_iff_mulVec.2 fun v => LinearMap.congr_fun hXY v)).1 h h
  have cr1 : CrOn φ (chRep (1 : G →* Eˣ)) H :=
    crUnr (A := ℚ_[l]) (φ.comp H.subtype) hψ
      (resCoef ℚ_[l] ((chRep (1 : G →* Eˣ)).comp H.subtype : Representation E H E))
      (by
        unfold ReciprocityTheory.Gal.ContAction
        simpa [resCoef, chRep] using continuous_snd) 0
      (fun g _ x => by simp [resCoef, chRep])
  have htw : twist (1 : G →* Eˣ)⁻¹ (adGL r) = adGL r := by
    refine MonoidHom.ext fun g => ?_
    simp [twist]
  have key : CrOn φ (colRep r) H →
      (CrOn φ (extRep (adGL r) y hy.2) H ↔ y ∈ UpperTheory.V.Loc.finiteCocycles φ (adGL r)) := fun h => by
    have := crExt φ hφ (adGL r) (extRep (adGL r) y hy.2) cM cH 1 (LinearMap.inl E _ E) (LinearMap.snd E _ E)
      (0, 1) y LinearMap.inl_injective (Function.Exact.inl_snd) rfl
      (fun g x => by simp [extRep_apply]) (fun g => by simp [extRep_apply]) H hH (crM h) cr1
    rwa [htw] at this
  constructor
  · intro hW
    have hV : CrOn φ (colRep r) H := by
      refine ((isCrys_isDR_sub_quot (φ.comp H.subtype) hψ _ _ (contAction_sub _ cW H) (contAction_sub _ cV H)
        (((TrivSqZeroExt.fstHom ℚ_[l] E E).toLinearMap).compLeft (Fin n)) (fun g x => ?_)).2 (fun v => ?_)).1 hW
      · funext i
        exact mulVec_fst _ _ _ (hr' g) x i
      · exact ⟨fun i => TrivSqZeroExt.inl (v i), rfl⟩
    refine ⟨hV, ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : y = 0 := Subsingleton.elim _ _
      rw [this]; exact Submodule.zero_mem _
    · refine (key hV).1 ?_
      refine (isCrys_isDR_internalHom (A := ℚ_[l]) (φ.comp H.subtype) hψ
        (resCoef ℚ_[l] ((colRep r).comp H.subtype : Representation E H _))
        (resCoef ℚ_[l] ((colRep r').comp H.subtype : Representation (DualNumber E) H _))
        (resCoef ℚ_[l] ((extRep (adGL r) y hy.2).comp H.subtype : Representation E H _))
        (contAction_sub _ cV H) (contAction_sub _ cW H) (contAction_sub _ cH H) (pair ℚ_[l] n)
        (fun g w v => hb g w v) (fun w w' h => ?_)).1 hV hW
      refine Prod.ext (Matrix.ext_iff_mulVec.2 fun v => funext fun i => ?_) ?_
      · rw [← pair_snd ℚ_[l], ← pair_snd ℚ_[l], h]
      · have := pair_fst ℚ_[l] n w 1 ⟨0, hn⟩
        rw [h, pair_fst] at this
        simpa using this.symm
  · rintro ⟨hV, hy'⟩
    refine (admissible_of_bilinear_openSubgroup_galois (A := ℚ_[l]) (φ.comp H.subtype) hψ
        (resCoef ℚ_[l] ((extRep (adGL r) y hy.2).comp H.subtype : Representation E H _))
        (resCoef ℚ_[l] ((colRep r).comp H.subtype : Representation E H _))
        (resCoef ℚ_[l] ((colRep r').comp H.subtype : Representation (DualNumber E) H _))
        (contAction_sub _ cH H) (contAction_sub _ cV H) (contAction_sub _ cW H) (pair ℚ_[l] n)
        (fun g w v => hb g w v) ?_).1 ((key hV).2 hy') hV
    refine eq_top_iff.2 fun x _ => ?_
    have : x = pair ℚ_[l] n (0, 1) (fun i => (x i).fst) + pair ℚ_[l] n (1, 0) (fun i => (x i).snd) := by
      funext i
      refine TrivSqZeroExt.ext ?_ ?_ <;> simp [pair_fst, pair_snd]
    rw [this]
    exact Submodule.add_mem _ (Submodule.subset_span ⟨(_, _), rfl⟩) (Submodule.subset_span ⟨(_, _), rfl⟩)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem grows_le {l : ℕ} (hl : 1 < l) {a : ℕ → ℕ} {s t : ℕ} (h : Grows l a s) (h' : Grows l a t) :
    s ≤ t := by
  obtain ⟨_, h⟩ := h
  obtain ⟨C, h'⟩ := h'
  have := (Nat.pow_le_pow_iff_right hl).1 ((h (C + 1) C.succ_pos).1.trans (h' (C + 1) C.succ_pos).2)
  by_contra hc
  have : (C + 1) * (t + 1) ≤ (C + 1) * s := Nat.mul_le_mul_left _ (by omega)
  nlinarith

private theorem grows_unique {l : ℕ} (hl : 1 < l) {a b : ℕ → ℕ} {s t : ℕ} (h : Grows l a s) (h' : Grows l b t)
    (e : ∀ m, a m = b m) : s = t := by
  obtain rfl : a = b := funext e
  exact le_antisymm (grows_le hl h h') (grows_le hl h' h)

private theorem grows_mul {l : ℕ} {a b : ℕ → ℕ} {s t : ℕ} (h : Grows l a s) (h' : Grows l b t) :
    Grows l (fun m => a m * b m) (s + t) := by
  obtain ⟨C, h⟩ := h
  obtain ⟨D, h'⟩ := h'
  refine ⟨C + D, fun m hm => ⟨?_, ?_⟩⟩
  · rw [mul_add, pow_add]
    exact Nat.mul_le_mul (h m hm).1 (h' m hm).1
  · rw [show m * (s + t) + (C + D) = (m * s + C) + (m * t + D) by ring, pow_add]
    exact Nat.mul_le_mul (h m hm).2 (h' m hm).2

private theorem grows_pow (l n d : ℕ) : Grows l (fun m => (l ^ (m * n)) ^ d) (d * n) :=
  ⟨0, fun m _ => by
    have : (l ^ (m * n)) ^ d = l ^ (m * (d * n)) := by rw [← pow_mul]; congr 1; ring
    simp [this]⟩

private theorem tate_lattice {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {χ : G →* ℤ_[l]ˣ} {d : ℕ} (hF : FinLevel l G χ d) {n : ℕ}
    (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) :
    Module.Finite ℤ_[l] (H1 ρ) ∧ Module.Finite ℤ_[l] (H2 ρ) ∧
      finrank ℤ_[l] (H1 ρ) = finrank ℤ_[l] ↥(H0 ρ) + finrank ℤ_[l] (H2 ρ) + d * n ∧
      finrank ℤ_[l] (H2 ρ) = finrank ℤ_[l] ((Fin n → ℤ_[l]) ⧸ coSub χ ρ) := by
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have hm := fun m => hF _ (redRep ρ m) (contAction_redRep h m)
  obtain ⟨f1, f2, g0, g1, g2⟩ := UpperTheory.lattice_cohomology_finite_and_growth_of_finGen ρ h (UpperTheory.latticeCochains_finGen_of_finLevel hF ρ h) fun m => ⟨(hm m).1, (hm m).2.1⟩
  refine ⟨f1, f2, grows_unique hl g1 (grows_mul (grows_mul g0 g2) (grows_pow l n d)) fun m => ?_,
    grows_unique hl g2 (UpperTheory.card_quotient_powSubmodule_grows_finrank l _) fun m => ?_⟩
  · rw [(hm m).2.2.2.1, card_quot_lSub]
  · rw [(hm m).2.2.2.2, UpperTheory.card_coinvariants_mod_pow_eq_mod_pow_coinvariants]

private theorem tate_Q {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] {χ : G →* ℤ_[l]ˣ} {d : ℕ} (hF : FinLevel l G χ d)
    {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V]
    [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul ℚ_[l] V]
    (ρ : Representation ℚ_[l] G V) (h : ContAction ρ) :
    Module.Finite ℚ_[l] (H1 ρ) ∧ Module.Finite ℚ_[l] (H2 ρ) ∧
      finrank ℚ_[l] (H1 ρ) = finrank ℚ_[l] ↥(H0 ρ) + finrank ℚ_[l] (H2 ρ) + d * finrank ℚ_[l] V ∧
      finrank ℚ_[l] (H2 ρ) =
        finrank ℚ_[l] (V ⧸ coSub ((Units.map (algebraMap ℤ_[l] ℚ_[l] : ℤ_[l] →* ℚ_[l])).comp χ) ρ) := by
  letI : Module ℤ_[l] V := Module.compHom V (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨ρT, j, hT, hj, he, hs⟩ := UpperTheory.exists_invariant_lattice_openEmbedding ρ h
  obtain ⟨r0, r1, r2⟩ := UpperTheory.rank_cohomology_rational_eq_rank_lattice ρ h ρT j hT hj he hs
  obtain ⟨f1, f2, e1, e2⟩ := tate_lattice hF ρT hT
  have q0 : finrank ℚ_[l] ↥(H0 ρ) = finrank ℤ_[l] ↥(H0 ρT) := congrArg Cardinal.toNat r0
  have q1 : finrank ℚ_[l] (H1 ρ) = finrank ℤ_[l] (H1 ρT) := congrArg Cardinal.toNat r1
  have q2 : finrank ℚ_[l] (H2 ρ) = finrank ℤ_[l] (H2 ρT) := congrArg Cardinal.toNat r2
  refine ⟨Module.rank_lt_aleph0_iff.1 (r1 ▸ Module.rank_lt_aleph0 _ _),
    Module.rank_lt_aleph0_iff.1 (r2 ▸ Module.rank_lt_aleph0 _ _), ?_, ?_⟩
  · rw [q0, q1, q2, e1]
  · rw [q2, e2, UpperTheory.finrank_coinvariants_eq_finrank_lattice_coinvariants χ ρ ρT j hj.injective he hs]

private theorem finrank_H0dual {G E V : Type} [Group G] [Field E] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] (χ : G →* Eˣ) (ρ : Representation E G V) :
    finrank E ↥(H0dual χ ρ) = finrank E (V ⧸ coSub χ ρ) := by
  have : H0dual χ ρ = (coSub χ ρ).dualAnnihilator := by
    ext f
    rw [Submodule.mem_dualAnnihilator]
    constructor
    · intro hf w hw
      refine (Submodule.span_le (p := LinearMap.ker f)).2 ?_ hw
      rintro _ ⟨g, x, rfl⟩
      simp [hf g x]
    · intro hf g x
      have := hf _ (Submodule.subset_span ⟨g, x, rfl⟩)
      simpa [sub_eq_zero] using this
  rw [this, ← (Submodule.dualQuotEquivDualAnnihilator _).finrank_eq, Subspace.dual_finrank_eq]

private theorem coSub_res {Q E G V : Type} [Field Q] [Field E] [Algebra Q E] [Group G] [AddCommGroup V]
    [Module E V] [Module Q V] [IsScalarTower Q E V] (χ : G →* Qˣ) (χ' : G →* Eˣ)
    (hχ : ∀ g, ((χ' g : Eˣ) : E) = algebraMap Q E (χ g : Qˣ)) (ρ : Representation E G V) :
    coSub χ (resCoef Q ρ) = (coSub χ' ρ).restrictScalars Q := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨g, x, rfl⟩
    exact Submodule.subset_span ⟨g, x, by rw [hχ, algebraMap_smul]; rfl⟩
  · intro y hy
    have key : ∀ c : E, c • y ∈ coSub χ (resCoef Q ρ) := by
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨g, x, rfl⟩ := hy
        intro c
        refine Submodule.subset_span ⟨g, c • x, ?_⟩
        change _ = ρ g (c • x) - _
        rw [hχ, algebraMap_smul, smul_sub, map_smul, smul_comm c (χ g : Q)]
      | zero => intro c; simp
      | add a b _ _ ha hb => intro c; rw [smul_add]; exact add_mem (ha c) (hb c)
      | smul a b _ hb => intro c; rw [smul_smul]; exact hb _
    simpa using key 1

theorem UpperTheory.V.Loc.tateRat :
    LocalPublishedTheorems → ∀ {v l : ℕ} [Fact v.Prime] [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ v) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V] (ρ : Representation E G V), ContAction ρ → Module.Finite E (H1 ρ) ∧ Module.Finite E (H2 ρ) ∧ finrank E (H1 ρ) = finrank E ↥(H0 ρ) + finrank E (H2 ρ) + (if v = l then φ.range.index * finrank E V else 0) ∧ finrank E (H2 ρ) = finrank E ↥(H0dual ((cycA v l E).comp φ) ρ) := by
  intro hP v l _ _ G _ _ _ φ hφ E _ _ _ _ _ V _ _ _ _ _ _ _ _ _ ρ h
  haveI : CompactSpace G := by
    have hc : IsClosed (φ.range : Set (GQ v)) := φ.range.isClosed_of_isOpen hφ.isOpen_range
    exact (⟨hφ.isEmbedding, hc⟩ : IsClosedEmbedding φ).compactSpace
  haveI : ContinuousConstSMul ℚ_[l] V := ⟨fun c => by
    simpa only [algebraMap_smul] using continuous_const_smul (T := V) (algebraMap ℚ_[l] E c)⟩
  haveI : FiniteDimensional E V := Module.Finite.of_restrictScalars_finite ℚ_[l] E V
  obtain ⟨f1, f2, e1, e2⟩ := tate_Q (UpperTheory.finite_level_of_finite_level_mod l G _ _ (UpperTheory.finiteLevel_cyclotomic_of_openEmbedding hP φ hφ)) (resCoef ℚ_[l] ρ) h
  obtain ⟨⟨a0⟩, ⟨a1⟩, ⟨a2⟩, -⟩ := UpperTheory.nonempty_cohomology_restrictScalars_linearEquiv ℚ_[l] ρ
  haveI := Module.Finite.equiv a1
  haveI := Module.Finite.equiv a2
  have hd : 0 < finrank ℚ_[l] E := finrank_pos
  rw [coSub_res ((Units.map (algebraMap ℤ_[l] ℚ_[l] : ℤ_[l] →* ℚ_[l])).comp ((cyc v l).comp φ))
      ((cycA v l E).comp φ)
      (fun g => IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] E ((cyc v l (φ g) : ℤ_[l]ˣ) : ℤ_[l])) ρ,
    (Submodule.Quotient.restrictScalarsEquiv ℚ_[l] _).finrank_eq, a2.finrank_eq,
    ← finrank_mul_finrank ℚ_[l] E (H2 ρ), ← finrank_mul_finrank ℚ_[l] E (V ⧸ _)] at e2
  rw [a0.finrank_eq, a1.finrank_eq, a2.finrank_eq, ← finrank_mul_finrank ℚ_[l] E (H2 ρ),
    ← finrank_mul_finrank ℚ_[l] E (H1 ρ), ← finrank_mul_finrank ℚ_[l] E ↥(H0 ρ),
    ← finrank_mul_finrank ℚ_[l] E V] at e1
  refine ⟨Module.Finite.of_restrictScalars_finite ℚ_[l] E _, Module.Finite.of_restrictScalars_finite ℚ_[l] E _,
    Nat.eq_of_mul_eq_mul_left hd ?_, ?_⟩
  · rw [e1]
    split_ifs <;> ring
  · rw [finrank_H0dual]
    exact Nat.eq_of_mul_eq_mul_left hd e2
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

theorem UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] (a b : G →* Bˣ), Continuous (fun g => (a g : B)) → Continuous (fun g => (b g : B)) → ∀ (x : G → B) (hx : ∀ g h, x (g * h) = x g + ((a / b) g : Bˣ) * x h), Continuous x → IsCr φ (chRep a) → IsCr φ (chRep b) → (IsCr φ (ext2 a b x hx) ↔ x ∈ UpperTheory.V.Loc.finiteCocycles φ (chRep (a / b))) := by
  intro l _ G _ _ _ φ hφ B _ _ _ _ _ _ a b ha hb x hx hc h1 h2
  have key := UpperTheory.V.Loc.crExt φ hφ (chRep a) (ext2 a b x hx) (contAction_chRep ha) (contAction_charExtension_of_continuous_cocycle ha hb hx hc)
    b (LinearMap.inl B B B) (LinearMap.snd B B B) (0, 1) x LinearMap.inl_injective Function.Exact.inl_snd rfl
    (fun g v => by simp [characterExtensionRep_apply, chRep_apply]) (fun g => by simp [characterExtensionRep_apply, mul_comm])
    ⊤ (by simp) ((crOn_top φ _).2 h1) ((crOn_top φ _).2 h2)
  have e : twist b⁻¹ (chRep a) = chRep (a / b) := by
    refine MonoidHom.ext fun g => LinearMap.ext fun v => ?_
    rw [twist_apply, chRep_apply, chRep_apply, div_eq_mul_inv, MonoidHom.mul_apply, Units.val_mul, smul_eq_mul]
    ring
  rwa [crOn_top, e] at key
end
