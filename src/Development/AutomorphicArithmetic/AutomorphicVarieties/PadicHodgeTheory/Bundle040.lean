module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle547
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle289
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle056
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle362
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle296
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LiftChart
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SpLiftL
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TangentSpaceDeformationAtL
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle014
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem charpoly_of_exact {K M₀ M M₂ : Type} [Field K] [AddCommGroup M₀] [Module K M₀] [FiniteDimensional K M₀]
    [AddCommGroup M] [Module K M] [FiniteDimensional K M] [AddCommGroup M₂] [Module K M₂] [FiniteDimensional K M₂]
    (f : M₀ →ₗ[K] M) (p : M →ₗ[K] M₂) (hf : Function.Injective f) (hp : Function.Surjective p)
    (he : Function.Exact f p) (T₀ : End K M₀) (T : End K M) (T₂ : End K M₂) (h₀ : ∀ x, f (T₀ x) = T (f x))
    (h₂ : ∀ x, p (T x) = T₂ (p x)) : T.charpoly = T₀.charpoly * T₂.charpoly := by
  have hA : ∀ x ∈ LinearMap.ker p, T x ∈ LinearMap.ker p := fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢; rw [h₂, hx, map_zero]
  rw [GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ (LinearMap.ker p) T hA]
  congr 1
  · let e : M₀ ≃ₗ[K] ↥(LinearMap.ker p) :=
      (LinearEquiv.ofInjective f hf).trans (LinearEquiv.ofEq _ _ (LinearMap.exact_iff.1 he).symm)
    have he' : T.restrict hA = e.conj T₀ := by
      refine LinearMap.ext fun y => ?_
      obtain ⟨x, rfl⟩ := e.surjective y
      rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      exact Subtype.ext (h₀ x).symm
    rw [he', LinearEquiv.charpoly_conj]
  · let e := p.quotKerEquivOfSurjective hp
    have he' : (LinearMap.ker p).mapQ (LinearMap.ker p) T (fun x hx => hA x hx) = e.symm.conj T₂ := by
      refine LinearMap.ext fun y => ?_
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
      rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.symm_symm]
      apply e.injective
      rw [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, Submodule.mkQ_apply, Submodule.mapQ_apply]
      simp only [e, LinearMap.quotKerEquivOfSurjective_apply_mk, h₂]
      rfl
    rw [he', LinearEquiv.charpoly_conj]

private theorem wdAt_of_model {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
    {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (B : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces B) {a : ℕ}
    (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) (L₂ : FinExt l) (r₂ : ↥(Dec (F := E) A) →* GL (Fin a) ↥L₂.1)
    (hm₂ : IsModel B r L₂ r₂) (hV₂ : IsPst P (B.repE L₂ r₂)) :
    wdAt P ι B h hj r = wdPst P ι B h hj (B.repE L₂ r₂) := by
  obtain ⟨L₁, r₁, hm₁, hV₁, e₁⟩ := wdAt_of_isPstAt ι B h hj (r := r) ⟨L₂, r₂, hm₂, hV₂⟩
  have h₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have h₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have e := IsModel.unique B r (hm₁.enlarge h₁) (hm₂.enlarge h₂)
  have a₁ := GlobalTheory.T.potSemistableParameter_coefficientField_enlarge P ι B h hj h₁ r₁ hV₁
  have a₂ := GlobalTheory.T.potSemistableParameter_coefficientField_enlarge P ι B h hj h₂ r₂ hV₂
  rw [e] at a₁
  exact e₁.trans (a₁.symm.trans a₂)

section Blocks

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (B : LocBridge l E Ω Gw O)

private theorem exists_model {m : ℕ} (r : ↥Gw →* GL (Fin m) (Om l)) (L : FinExt l) (hL : B.LL.1 ≤ L.1)
    (hr : ∀ g i j, (r g : Matrix (Fin m) (Fin m) (Om l)) i j ∈ L.1) : ∃ r₂, IsModel B r L r₂ := by
  let M : ↥Gw →* Matrix (Fin m) (Fin m) ↥L.1 :=
    { toFun := fun g => Matrix.of fun i j => ⟨_, hr g i j⟩
      map_one' := by
        ext i j
        simp [Matrix.one_apply, apply_ite]
      map_mul' := fun g g' => by
        ext i j
        simp [Matrix.mul_apply] }
  exact ⟨M.toHomUnits, hL, by ext g i j; rfl⟩

private theorem blocks {n : ℕ} (r : ↥Gw →* GL (Fin (n + 1)) (Om l)) (r' : ↥Gw →* GL (Fin n) (Om l))
    (ψ : ↥Gw →* (Om l)ˣ)
    (h0 : ∀ g (i : Fin n), (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Om l)) i.succ 0 = 0)
    (h1 : ∀ g, (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Om l)) 0 0 = (ψ g : Om l))
    (h2 : ∀ g (i j : Fin n), (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Om l)) i.succ j.succ =
      (r' g : Matrix (Fin n) (Fin n) (Om l)) i j)
    (L : FinExt l) (r₁ : ↥Gw →* GL (Fin (n + 1)) ↥L.1) (hm : IsModel B r L r₁) :
    ∃ (r₀ : ↥Gw →* GL (Fin 1) ↥L.1) (r₂ : ↥Gw →* GL (Fin n) ↥L.1)
      (f : (Fin 1 → ↥L.1) →ₗ[↥L.1] (Fin (n + 1) → ↥L.1)) (p : (Fin (n + 1) → ↥L.1) →ₗ[↥L.1] (Fin n → ↥L.1)),
      IsModel B (GlobalTheory.TripleGal.rk1 ψ) L r₀ ∧ IsModel B r' L r₂ ∧
      (∀ g v, f (B.repE L r₀ g v) = B.repE L r₁ g (f v)) ∧ (∀ g v, p (B.repE L r₁ g v) = B.repE L r₂ g (p v)) ∧
      Function.Injective f ∧ Function.Surjective p ∧ Function.Exact f p := by
  have e₁ : ∀ g i j, (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Om l)) i j =
      (((r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) ↥L.1) i j : ↥L.1) : Om l) := fun g i j => by rw [← hm.2]; rfl
  have eψ : ∀ g i j, (GlobalTheory.TripleGal.rk1 ψ g : Matrix (Fin 1) (Fin 1) (Om l)) i j = ψ g := fun g i j => by
    rw [Subsingleton.elim j i]
    exact Matrix.diagonal_apply_eq (fun _ : Fin 1 => (ψ g : Om l)) i
  obtain ⟨r₀, m₀⟩ := exists_model B (GlobalTheory.TripleGal.rk1 ψ) L hm.1 fun g i j => by
    rw [eψ, ← h1, e₁]; exact SetLike.coe_mem _
  obtain ⟨r₂, m₂⟩ := exists_model B r' L hm.1 fun g i j => by
    rw [← h2, e₁]; exact SetLike.coe_mem _
  have k0 : ∀ g (i : Fin n), (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) ↥L.1) i.succ 0 = 0 :=
    fun g i => Subtype.ext ((e₁ g _ _).symm.trans (h0 g i))
  have k1 : ∀ g, (r₀ g : Matrix (Fin 1) (Fin 1) ↥L.1) 0 0 = (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) ↥L.1) 0 0 :=
    fun g => Subtype.ext (by rw [← e₁, h1, ← eψ g 0 0, ← m₀.2]; rfl)
  have k2 : ∀ g i j, (r₂ g : Matrix (Fin n) (Fin n) ↥L.1) i j =
      (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) ↥L.1) i.succ j.succ :=
    fun g i j => Subtype.ext (by rw [← e₁, h2, ← m₂.2]; rfl)
  have ap : ∀ {m : ℕ} (s : ↥Gw →* GL (Fin m) ↥L.1) g v i,
      B.repE L s g v i = ∑ j, (s (B.e.symm g) : Matrix (Fin m) (Fin m) ↥L.1) i j * v j := fun s g v i => rfl
  refine ⟨r₀, r₂, LinearMap.single ↥L.1 (fun _ => ↥L.1) 0 ∘ₗ LinearMap.proj 0, LinearMap.funLeft ↥L.1 ↥L.1 Fin.succ,
    m₀, m₂, fun g v => funext fun i => ?_, fun g v => funext fun i => ?_, fun x y hxy => funext fun i => ?_,
    LinearMap.funLeft_surjective_of_injective _ _ _ (Fin.succ_injective n), fun x => ⟨fun hx => ?_, ?_⟩⟩
  · rw [ap]
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [ap, k1, Fin.sum_univ_succ]
    · simp [k0, Fin.sum_univ_succ]
  · rw [ap, LinearMap.funLeft_apply, ap, Fin.sum_univ_succ, k0]
    simp [k2]
  · rw [Subsingleton.elim i 0]
    simpa using congrFun hxy 0
  · refine ⟨fun _ => x 0, funext fun i => ?_⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · simp
    · simpa using (congrFun hx i).symm
  · rintro ⟨y, rfl⟩
    funext i
    simp

end Blocks


theorem UpperTheory.deRham_rational_of_extension_by_character :
    GlobalTheory.Published.DeRhamPotSemistable → ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) {n : ℕ} (r : ↥(Dec (F := F) A) →* GL (Fin (n + 1)) (Qbar l)) (r' : ↥(Dec (F := F) A) →* GL (Fin n) (Qbar l)) (ψ : ↥(Dec (F := F) A) →* (Qbar l)ˣ), Continuous r → (∀ g (i : Fin n), (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Qbar l)) i.succ 0 = 0) → (∀ g, (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Qbar l)) 0 0 = (ψ g : Qbar l)) → (∀ g (i j : Fin n), (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Qbar l)) i.succ j.succ = (r' g : Matrix (Fin n) (Fin n) (Qbar l)) i j) → ∀ (c : (F →+* Qbar l) → ℤ) (HT : (F →+* Qbar l) → Multiset ℤ) (β : ↥(Weil h) → ℂ) (Q : ↥(Weil h) → ℂ[X]), DRat ι h r (fun τ => c τ ::ₘ HT τ) (fun s => (X - C (β s)) * Q s) → DRat ι h (GlobalTheory.TripleGal.rk1 ψ) (fun τ => {c τ}) (fun s => X - C (β s)) → DRat ι h r' HT Q := by
  intro hB F Ω _ _ _ _ _ l _ ι A w h n r r' ψ hc h0 h1 h2 c HT β Q hr hψ O _ _ _ Bw hj
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  obtain ⟨d₁, j₁, p₁⟩ := hr O Bw hj
  obtain ⟨-, j₀, p₀⟩ := hψ O Bw hj
  have dr : ∀ {m : ℕ} (L : FinExt l) (s : ↥(Dec (F := F) A) →* GL (Fin m) ↥L.1),
      IsDR ((UpperTheory.V.Loc.PP l).PD Bw.Kw) (Bw.repE L s) ↔ Bw.IsdRE (UpperTheory.V.Loc.PP l) L s := fun L s => by
    rw [IsDR, finrank_fin_fun]; rfl
  refine ⟨?_, fun τ LL' τ' hτ => ?_, fun s => ?_⟩
  · obtain ⟨L, r₁, hm, hd⟩ := d₁
    obtain ⟨r₀, r₂, f, p, -, m₂, hf, hp, fi, ps, ex⟩ := blocks Bw r r' ψ h0 h1 h2 L r₁ hm
    exact ⟨L, r₂, m₂, (dr L r₂).1 (GlobalTheory.Per.ExactMult.exact_hodge_add l _ _ T Bw.Kw L _ _ _ _ _ _ f p hf hp
      fi ps (LinearMap.exact_iff.1 ex).symm ((dr L r₁).2 hd)).2.1⟩
  · obtain ⟨L, r₁, hm, hd, τ₁, t₁, hcount⟩ := j₁ τ LL' τ' hτ
    obtain ⟨r₀, r₂, f, p, m₀, m₂, hf, hp, fi, ps, ex⟩ := blocks Bw r r' ψ h0 h1 h2 L r₁ hm
    obtain ⟨-, d₂, hadd⟩ := GlobalTheory.Per.ExactMult.exact_hodge_add l _ _ T Bw.Kw L _ _ _ _ _ _ f p hf hp
      fi ps (LinearMap.exact_iff.1 ex).symm ((dr L r₁).2 hd)
    refine ⟨L, r₂, m₂, (dr L r₂).1 d₂, τ₁, t₁, fun a => ?_⟩
    have a₀ := IsJumpsAt.count_eq (UpperTheory.V.Loc.PP l) m₀ t₁ (j₀ τ LL' τ' hτ) a
    have a₁ := hcount a
    have a₂ : Bw.multE (UpperTheory.V.Loc.PP l) L r₁ τ₁ a = Bw.multE (UpperTheory.V.Loc.PP l) L r₀ τ₁ a + Bw.multE (UpperTheory.V.Loc.PP l) L r₂ τ₁ a :=
      (hadd τ₁ a).2.1
    beta_reduce at a₀ a₁
    rw [← Multiset.singleton_add, Multiset.count_add, Nat.cast_add, a₀, a₂] at a₁
    exact add_left_cancel a₁
  · obtain ⟨L, r₁, hm, hV⟩ := hB.isPstAt T Bw r (Units.continuous_val.comp hc) d₁
    obtain ⟨r₀, r₂, f, p, m₀, m₂, hf, hp, fi, ps, ex⟩ := blocks Bw r r' ψ h0 h1 h2 L r₁ hm
    obtain ⟨V₀, V₂, wi, ws, wex⟩ := UpperTheory.weil_deligne_functor_exactness l ι Bw.Kw L _ _ _ _ _ _ f p hf hp fi ps ex hV
    haveI := hV.finite
    haveI := V₀.finite
    haveI := V₂.finite
    have a₀ := p₀ s
    have a₁ := p₁ s
    beta_reduce at a₀ a₁
    rw [wdAt_of_model _ ι Bw h hj _ L r₀ m₀ V₀, DpstMap.charPol_wdPst _ ι Bw h hj _ V₀] at a₀
    rw [wdAt_of_model _ ι Bw h hj _ L r₁ hm hV, DpstMap.charPol_wdPst _ ι Bw h hj _ hV,
      charpoly_of_exact _ _ wi ws wex _ _ _ (DpstMap.wdLin_wdRho _ ι Bw h hj hf s)
        (DpstMap.wdLin_wdRho _ ι Bw h hj hp s), a₀] at a₁
    rw [wdAt_of_model _ ι Bw h hj _ L r₂ m₂ V₂, DpstMap.charPol_wdPst _ ι Bw h hj _ V₂]
    exact mul_left_cancel₀ (X_sub_C_ne_zero _) a₁
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.deRhamRational_of_conj :
    GlobalTheory.Published.DeRhamPotSemistable → ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) {n : ℕ} (r r' : ↥(Dec (F := F) A) →* GL (Fin n) (Qbar l)) (p : GL (Fin n) (Qbar l)), Continuous r → (∀ g, r' g = p * r g * p⁻¹) → ∀ (HT : (F →+* Qbar l) → Multiset ℤ) (Q : ↥(Weil h) → ℂ[X]), DRat ι h r HT Q → DRat ι h r' HT Q := by
  intro hD F Ω _ _ _ _ _ l _ ι A w h n r r' p hc e HT Q H O _ _ _ Bw hj
  obtain ⟨h1, h2, h3⟩ := H O Bw hj
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  obtain ⟨c1, -, -, c4⟩ := GlobalTheory.ConjLocal.local_conj l (UpperTheory.V.Loc.PP l) F Ω O _ Bw n _ _ p e
  have hp := hD.isPstAt T Bw r (Units.continuous_val.comp hc) h1
  have hw := (GlobalTheory.PstConj.main F Ω l ι n _ _ ⟨T⟩ w A h O Bw hj r r' p e hp).2
  exact ⟨c1 h1, fun τ L τ' hτ => c4 _ _ (h2 τ L τ' hτ), fun s => by rw [hw]; exact h3 s⟩
end

section

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

section Gen

variable {R K H : Type} [CommRing R] [CommRing K] [Group H]

private theorem cl_prj (f : R →+* K) (F : M4 R →+* M4 K) (hF : ∀ (a : R) X, F (a • X) = f a • F X)
    (c : Fin 4 → R) (X : M4 R) (i : Fin 4) : prj (fun a => f (c a)) (F X) i = F (prj c X i) := by
  unfold prj
  have h : ∀ p : Polynomial R, Polynomial.aeval (F X) (p.map f) = F (Polynomial.aeval X p) := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [Polynomial.map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
    | monomial n a =>
      rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial, map_mul, map_pow,
        Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, hF, map_one]
  rw [← h, Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

private theorem cl_eqs (f : R →+* K) (F : M4 R →+* M4 K) (hF : ∀ (a : R) X, F (a • X) = f a • F X)
    (hadj : ∀ X, adj (F X) = F (adj X)) (hch : ∀ X : M4 R, (F X).charpoly = X.charpoly.map f)
    (I : Subgroup H) (ν : H → R) (ps : Fin 4 → H → R) (s₀ : H) (r : H →* M4 R) (r' : H →* M4 K)
    (hr : ∀ g, r' g = F (r g)) :
    ((∀ g, IsGSp (ν g) (r g)) ∧ Ord I ps s₀ r →
      (∀ g, IsGSp (f (ν g)) (r' g)) ∧ Ord I (fun i g => f (ps i g)) s₀ r') ∧
    (Function.Injective f → Function.Injective F →
      (∀ g, IsGSp (f (ν g)) (r' g)) ∧ Ord I (fun i g => f (ps i g)) s₀ r' →
      (∀ g, IsGSp (ν g) (r g)) ∧ Ord I ps s₀ r) := by
  have e0 : ∀ g, adj (r' g) * r' g = F (adj (r g) * r g) := fun g => by rw [hr, hadj, map_mul]
  have e1 : ∀ a : R, f a • (1 : M4 K) = F (a • 1) := fun a => by rw [hF, map_one]
  have e2 : (∏ j, (Polynomial.X - Polynomial.C (f (ps j s₀)))) =
      (∏ j, (Polynomial.X - Polynomial.C (ps j s₀))).map f := by
    rw [Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  have e3 : ∀ i, prj (fun a => f (ps a s₀)) (r' s₀) i = F (prj (fun a => ps a s₀) (r s₀) i) := fun i => by
    rw [hr, cl_prj f F hF (fun a => ps a s₀)]
  refine ⟨fun ⟨h1, h⟩ => ⟨fun g => ?_, ?_, fun g i j hij => ?_, fun s hs i => ?_⟩,
    fun hf hi ⟨h1, h⟩ => ⟨fun g => hi ?_, Polynomial.map_injective f hf ?_, fun g i j hij => hi ?_,
      fun s hs i => hi ?_⟩⟩
  · exact (e0 g).trans ((congrArg F (h1 g)).trans (e1 _).symm)
  · rw [hr, hch, h.charpoly, e2]
  · rw [e3, e3, hr, ← map_mul, ← map_mul, h.stable g i j hij, map_zero]
  · rw [e3, hr s, e1, ← map_sub, ← map_mul, ← map_mul, h.inert s hs i, map_zero]
  · exact (e0 g).symm.trans ((h1 g).trans (e1 _))
  · rw [← hch, ← hr, h.charpoly, e2]
  · rw [map_mul, map_mul, ← e3, ← e3, ← hr, h.stable g i j hij, map_zero]
  · rw [map_mul, map_mul, map_sub, ← e3, ← hr, ← e1, h.inert s hs i, map_zero]

private theorem cl_map (f : R →+* K) (I : Subgroup H) (ν : H → R) (ps : Fin 4 → H → R) (s₀ : H) (r : H →* M4 R) :
    ((∀ g, IsGSp (ν g) (r g)) ∧ Ord I ps s₀ r →
      (∀ g, IsGSp (f (ν g)) (mapRep f r g)) ∧ Ord I (fun i g => f (ps i g)) s₀ (mapRep f r)) ∧
    (Function.Injective f →
      (∀ g, IsGSp (f (ν g)) (mapRep f r g)) ∧ Ord I (fun i g => f (ps i g)) s₀ (mapRep f r) →
      (∀ g, IsGSp (ν g) (r g)) ∧ Ord I ps s₀ r) := by
  have h := cl_eqs f f.mapMatrix (fun a X => by ext i j; simp)
    (fun X => by
      ext i j
      simp only [adj_apply, RingHom.mapMatrix_apply, Matrix.map_apply, map_zsmul])
    (fun X => Matrix.charpoly_map X f) I ν ps s₀ r (mapRep f r) fun _ => rfl
  exact ⟨h.1, fun hf => h.2 hf fun X Y e => Matrix.map_injective hf e⟩

private def cl_conj (τ : ℤ × ℤ → R) (h0 : τ 0 = 1) (hm : ∀ i j, τ (i + j) = τ i * τ j) : M4 R →+* M4 R where
  toFun X := Matrix.of fun a b => τ (wt a b) * X a b
  map_one' := by
    ext a b
    by_cases h : a = b
    · subst h
      simp [(wt_eq_zero a a).2 rfl, h0]
    · simp [Matrix.one_apply_ne h]
  map_mul' X Y := by
    ext a b
    simp only [Matrix.of_apply, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : wt a b = wt a k + wt k b := by simp [wt]
    rw [this, hm]
    ring
  map_zero' := by ext a b; simp
  map_add' X Y := by ext a b; simp [mul_add]

private theorem cl_tor (t : Multiplicative (ℤ × ℤ) →* Rˣ) (I : Subgroup H) (ν : H → R) (ps : Fin 4 → H → R) (s₀ : H)
    (r : H →* M4 R) (h : (∀ g, IsGSp (ν g) (r g)) ∧ Ord I ps s₀ r) :
    ∃ r' : H →* M4 R, (∀ g a b, r' g a b = t (Multiplicative.ofAdd (wt a b)) * r g a b) ∧
      (∀ g, IsGSp (ν g) (r' g)) ∧ Ord I ps s₀ r' := by
  let F := cl_conj (fun j => (t (Multiplicative.ofAdd j) : R)) (by simp) (fun i j => by simp [ofAdd_add])
  have hF : ∀ X a b, F X a b = t (Multiplicative.ofAdd (wt a b)) * X a b := fun _ _ _ => rfl
  refine ⟨F.toMonoidHom.comp r, fun _ _ _ => rfl,
    (cl_eqs (RingHom.id R) F (fun a X => ?_) (fun X => ?_) (fun X => ?_) I ν ps s₀ r _ fun _ => rfl).1 h⟩
  · ext i j
    simp [hF, mul_left_comm]
  · ext i j
    simp only [adj_apply, hF, wt_rev, mul_smul_comm]
  · let d : Fin 4 → Rˣ := fun a => t (Multiplicative.ofAdd (lamW a, muW a))
    let u : (M4 R)ˣ := ⟨Matrix.diagonal fun a => d a, Matrix.diagonal fun a => ((d a)⁻¹ : Rˣ),
      by simp [Matrix.diagonal_mul_diagonal], by simp [Matrix.diagonal_mul_diagonal]⟩
    have : F X = u.val * X * u⁻¹.val := by
      ext a b
      show _ = (Matrix.diagonal (fun a => (d a : R)) * X * Matrix.diagonal fun a => (((d a)⁻¹ : Rˣ) : R)) a b
      have e : wt a b = (lamW a, muW a) - (lamW b, muW b) := rfl
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hF, e, ofAdd_sub, map_div, div_eq_mul_inv, Units.val_mul]
      ring
    rw [this, Polynomial.map_id, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

end Gen

private theorem cl_count {n : ℕ} (u : Fin n → ℤ × ℤ) (h : ∀ j, Nat.card {i // u i = j} = dimsL j) : n = 14 := by
  classical
  have h1 : ∀ i, u i ∈ wts := fun i => by
    by_contra hn
    have h2 : dimsL (u i) = 0 := by
      unfold dimsL
      rw [if_neg, if_neg hn]
      rintro (e | e | e | e | e) <;> exact hn (by rw [e]; decide)
    haveI : Nonempty {k // u k = u i} := ⟨⟨i, rfl⟩⟩
    exact Nat.card_pos.ne' ((h _).trans h2)
  have h3 := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := wts) (f := u) fun i _ => h1 i
  have h4 : ∀ j, (Finset.univ.filter fun i => u i = j).card = dimsL j := fun j => by
    rw [← h j, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [h4, Finset.card_univ, Fintype.card_fin] at h3
  rw [h3]
  decide

theorem UpperTheory.V.Loc.spChartL :
    LocalPublishedTheorems → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (hD : D.Good) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra ↥c.O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ↥c.O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing ↥c.O E] (R : Type) [CommRing R] [Algebra ↥c.O R] [IsCO ↥c.O R] (ρ : Lift c.O (D.rbarAt l) R), Represents D.condL ρ → ∃ (x : R →ₐ[c.O] c.O) (P : Ideal R) (w : Fin 14 → ℤ × ℤ) (φ : R →ₐ[c.O] MvPowerSeries (Fin 14) E), (ρ.map x).hom = D.r0At l ∧ UpperTheory.V.Loc.IsCompl P x φ ∧ (∃ y, x y ≠ 0 ∧ ∀ a ∈ P, y * a = 0) ∧ (∀ j, Nat.card {i // w i = j} = dimsL j) ∧ ∀ g a b, φ (ρ.hom g a b) ∈ wtPart E w (wt a b) := by
  intro hP Ω _ _ _ l _ c D hD E _ _ _ _ _ _ _ _ R _ _ _ ρ hρ
  haveI : CompactSpace (D.Gp l) := isCompact_iff_compactSpace.1 (isClosed_Dec (F := ℚ) (D.pl l)).isCompact
  have hmap : ∀ (B B' : Type) [CommRing B] [Algebra c.O B] [CommRing B'] [Algebra c.O B'] (f : B →ₐ[c.O] B')
      (r : D.Gp l →* M4 B), (EqL D r → EqL D (mapRep (f : B →+* B') r)) ∧
        (Function.Injective f → EqL D (mapRep (f : B →+* B') r) → EqL D r) := by
    intro B B' _ _ _ _ f r
    have h := cl_map (f : B →+* B') ((D.Ip l).subgroupOf (D.Gp l)) (fun g => algebraMap c.O B (D.th g))
      (fun i g => algebraMap c.O B (D.ps i g)) D.s0 r
    have hy : ∀ a : c.O, (f : B →+* B') (algebraMap c.O B a) = algebraMap c.O B' a := fun a => f.commutes a
    simp only [hy] at h
    exact h
  obtain ⟨ρ₁, h₁, hpt⟩ := r0pt D hD
  have hr0 : (D.loc ρ₁ l).hom = D.r0At l := congrArg (fun r : G ℚ Ω →* M4 c.O => r.comp (D.Gp l).subtype) h₁
  have h0 : EqL D (D.loc ρ₁ l).hom := by
    obtain ⟨B, _, _, _, _, ρ', h1, -, y, hy⟩ := hpt.atL
    rw [← hy]
    exact (hmap B c.O y ρ'.hom).1 h1
  have hst : ρ.TStable fun a => (lamW a, muW a) := by
    intro R' _ _ _ f t ht
    obtain ⟨r', h1, h2⟩ := cl_tor t _ _ _ _ (ρ.map f).hom ((hρ R').1 f)
    let ρ' : Lift c.O (D.rbarAt l) R' :=
      { hom := r'
        cont := fun a b N => by
          simp only [h1, map_mul]
          exact ((ρ.map f).cont a b N).comp (_ * ·)
        red := fun g a b => by rw [h1, map_mul, ht, one_mul, (ρ.map f).red] }
    obtain ⟨f', hf', -⟩ := (hρ R').2 ρ' h2
    refine ⟨f', fun g a b => ?_⟩
    rw [hf']
    exact h1 g a b
  obtain ⟨x, P, n, u, φ, h1, h2, h3, h4, h5⟩ := liftChart (l := l) (D.rbarAt l) (fun a => (lamW a, muW a)) E R ρ
    (fun B _ _ r => EqL D r) hmap hρ hst (D.loc ρ₁ l) h0
    (fun g a b hab => by
      rw [hr0]
      exact Matrix.diagonal_apply_ne (fun i => (D.ps i g : c.O)) fun e : a = b => hab (by rw [e]))
    (fun B _ _ _ _ _ _ _ _ _ _ π hπ B' _ _ _ _ _ _ _ _ _ _ π' hπ' p hp hπp r' e1 e2 e3 => by
      obtain ⟨r, k1, k2, k3⟩ := spLiftL hP D hD E B π hπ B' π' hπ' p hp hπp r' ⟨hr0 ▸ e1, e2⟩ e3
      exact ⟨r, k1.cont, k2, k3⟩)
  have h6 : ∀ j, Nat.card {i // u i = j} = dimsL j := fun j => by
    obtain ⟨S, hS, hS'⟩ := h5 j
    rw [hr0] at hS'
    exact hS.trans (UpperTheory.tangent_space_deformation_at_l hP D hD E j S hS')
  obtain rfl := cl_count u h6
  exact ⟨x, P, u, φ, by rw [h1, hr0], h2, h3, h6, h4⟩
end
