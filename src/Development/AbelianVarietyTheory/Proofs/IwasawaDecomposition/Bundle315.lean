module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle301
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle296
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle509
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle304
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle178
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle179
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle191
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle301
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle303
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle306
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle307
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle309
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle308
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVecLowKSub
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle261

@[expose] public section

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU GlobalTheory.Branching

noncomputable section

namespace GlobalTheory.DefU

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def infSpan (φ : UA E n → ℂ) : Submodule ℂ (UA E n → ℂ) :=
  Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)

theorem RU_mem_infSpan (φ : UA E n → ℂ) {x : UA E n} (hx : x ∈ infU E n) {ψ : UA E n → ℂ} (hψ : ψ ∈ infSpan φ) :
    RU E n x ψ ∈ infSpan φ := by
  have : infSpan φ ≤ (infSpan φ).comap (RU E n x) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    show RU E n x (RU E n k φ) ∈ infSpan φ
    rw [RU_RU]
    exact Submodule.subset_span ⟨⟨x * k, mul_mem hx k.2⟩, rfl⟩
  exact this hψ

theorem mem_infU_of_mem_embU {τ : E →+* ℂ} {x : UA E n} (hx : x ∈ embU n τ) : x ∈ infU E n :=
  (Subgroup.mem_inf.1 hx).1

theorem exists_hasWeightAt (U : AutSub E n) (τ : E →+* ℂ) : ∃ lam, HasWeightAt U.V τ lam := by
  obtain ⟨e, he⟩ := GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E n τ
  obtain ⟨φ, hφU, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot U.isAut.ne_bot
  let j : Matrix.unitaryGroup (Fin n) ℂ →* UA E n := (embU n τ).subtype.comp e.symm.toMulEquiv.toMonoidHom
  have hj : ∀ u, j u ∈ infU E n := fun u => mem_infU_of_mem_embU (e.symm u).2
  let S := infSpan φ
  have hφS : φ ∈ S := by
    have : RU E n (1 : infU E n) φ ∈ S := Submodule.subset_span ⟨1, rfl⟩
    simpa using this
  have hS : S ≤ U.V := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact U.isAut.stable _ _ hφU)
  haveI : FiniteDimensional ℂ S := (U.isAut.aut φ hφU).kfin
  haveI : Nontrivial S := ⟨⟨⟨φ, hφS⟩, 0, fun h => hφ0 (congrArg Subtype.val h)⟩⟩
  let ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) S :=
    sub ((RU E n).comp j) S (fun u ψ hψ => RU_mem_infSpan φ (hj u) hψ)
  have hρ : ∀ u (v : S), (ρ u v : UA E n → ℂ) = RU E n (j u) v := fun _ _ => rfl
  have hcont : ∀ (l : Module.Dual ℂ S) (v : S), Continuous fun u => l (ρ u v) := by
    let P : Submodule ℂ (Module.Dual ℂ S) :=
      { carrier := {l | ∀ v : S, Continuous fun u => l (ρ u v)}
        add_mem' := fun ha hb v => (ha v).add (hb v)
        zero_mem' := fun _ => continuous_const
        smul_mem' := fun c _ ha v => (ha v).const_smul c }
    have hev : ∀ g : UA E n, (LinearMap.proj g ∘ₗ S.subtype : Module.Dual ℂ S) ∈ P := fun g v => by
      have hv : Continuous (v : UA E n → ℂ) := (U.isAut.aut _ (hS v.2)).cont
      have : Continuous fun u => (j u : UA E n) := continuous_subtype_val.comp e.symm.continuous
      exact hv.comp ((continuous_const_mul g).comp this)
    have h1 : P.dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_dualCoannihilator] at hv
      exact (Submodule.mem_bot ℂ).2 (Subtype.ext (funext fun g => hv _ (hev g)))
    have hP : P = ⊤ := by
      rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := P), h1, Submodule.dualAnnihilator_bot]
    intro l v
    have : l ∈ P := hP ▸ Submodule.mem_top
    exact this v
  obtain ⟨lam, f, hf⟩ := GlobalTheory.T.unitaryGroup_finiteDimensionalRep_contains_highestWeightRep n S ρ hcont
  refine ⟨lam, isIrreducible_smallRep_id n lam, S.subtype ∘ₗ f.toLinearMap, fun h0 => hf ?_,
    fun v => hS (f v).2, fun x v => ?_⟩
  · refine Representation.IntertwiningMap.ext (LinearMap.ext fun v => Subtype.ext ?_)
    simpa using LinearMap.congr_fun h0 v
  · have h1 : ((cEmb τ).comp (embU n τ).subtype) x = unitaryIncl n (e x) := (he x).symm
    rw [h1]
    have h2 := Representation.IntertwiningMap.isIntertwining _ _ f (e x) v
    change (f (smallRep (unitaryIncl n) lam (e x) v)).1 = _
    rw [h2, hρ]
    change RU E n ((e.symm (e x) : embU n τ) : UA E n) (f v).1 = _
    rw [e.symm_apply_apply]
    rfl

theorem hasWeightAt_unique (U : AutSub E n) (τ : E →+* ℂ) {lam lam' : DomWeight n} (h : HasWeightAt U.V τ lam)
    (h' : HasWeightAt U.V τ lam') : lam = lam' := by
  obtain ⟨e, he⟩ := GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E n τ
  obtain ⟨r, -, hr1, hr⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryArchimedeanPoints E n τ
  let s : Matrix.unitaryGroup (Fin n) ℂ →* UA E n := (embU n τ).subtype.comp e.symm.toMulEquiv.toMonoidHom
  have mk : ∀ mu, HasWeightAt U.V τ mu →
      ∃ f : (smallRep (unitaryIncl n) mu).IntertwiningMap (U.rep.comp s), f ≠ 0 := by
    rintro mu ⟨-, F, hF0, hFm, hFi⟩
    refine ⟨⟨F.codRestrict U.V hFm, fun u => ?_⟩, fun h0 => hF0 ?_⟩
    · ext v : 1
      apply Subtype.ext
      show F (sqRep ℂ n mu (unitaryIncl n u) v) = RU E n (s u) (F v)
      have : unitaryIncl n u = ((cEmb τ).comp (embU n τ).subtype) (e.symm u) := by
        have h3 := he (e.symm u)
        rw [e.apply_symm_apply] at h3
        exact h3
      rw [this, hFi]
      rfl
    · ext v : 1
      exact congrArg Subtype.val (DFunLike.congr_fun h0 v :)
  obtain ⟨f, hf⟩ := mk lam h
  obtain ⟨f', hf'⟩ := mk lam' h'
  have hc : ∀ g, ∃ u, ∀ y, Commute ((s u)⁻¹ * g) (s y) := fun g =>
    ⟨e (r g), fun y => by
      change Commute ((((e.symm (e (r g))) : embU n τ) : UA E n)⁻¹ * g) ((e.symm y : embU n τ) : UA E n)
      rw [e.symm_apply_apply]
      exact hr g _⟩
  obtain ⟨ee⟩ := (GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor _ _ _ _ _ U.rep s _ _ U.isIrreducible_rep (isIrreducible_smallRep_unitary n lam)
    (isIrreducible_smallRep_unitary n lam') hc f hf).2 f' hf'
  by_contra hne
  have h0 := intertwining_unitary_eq_zero n lam lam' hne ee.toIntertwiningMap
  obtain ⟨v, hv⟩ := exists_ne (0 : nablaSq ℂ n lam)
  exact hv (ee.injective ((DFunLike.congr_fun h0 v).trans (map_zero ee).symm))

theorem AU.existsUnique_hasWt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AU E n)
    (τ : E →+* ℂ), ∃! lam : DomWeight n, π.HasWt τ lam := by
  intro E _ _ _ n π τ
  obtain ⟨U, rfl⟩ := AU.mk_surjective π
  obtain ⟨lam, h⟩ := exists_hasWeightAt U τ
  exact ⟨lam, h, fun mu hmu => (hasWeightAt_unique U τ h hmu).symm⟩

end GlobalTheory.DefU

end
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

noncomputable section

namespace GlobalTheory.DefU.admitted

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem exists_fin_mul_inf (y : UA E n) : ∃ a ∈ finU (E := E) (n := n), ∃ b ∈ infU E n, y = a * b := by
  let yi := GeneralLinearGroup.map (pInf E) y.1
  have hyi : yi.valᴴ * yi.val = 1 := by
    have hy : cT (conjAd E) y.1.val * 1 * y.1.val = 1 := y.2
    have h3 : (cT (conjAd E) y.1.val).map (pInf E) = yi.valᴴ := by
      ext1 i j
      rw [Matrix.conjTranspose_apply]
      exact (infEq E).symm_apply_apply _
    have h := congrArg (pInf E).mapMatrix hy
    rw [map_mul, map_mul, map_one, mul_one, RingHom.mapMatrix_apply, h3] at h
    exact h
  let b : UA E n := ⟨infGL E n yi, infGL_mem_UA yi hyi⟩
  have hb : b ∈ infU E n := MonoidHom.mem_ker.2 (pFin_infGL yi)
  have ha : b⁻¹ * y ∈ finU (E := E) (n := n) := by
    refine MonoidHom.mem_ker.2 ?_
    rw [map_mul, map_inv]
    have : cInf b = cInf y := pInf_infGL yi
    rw [this, inv_mul_cancel]
  refine ⟨b⁻¹ * y, ha, b, hb, ?_⟩
  rw [fin_mul_inf ha hb, mul_inv_cancel_left]

def X (φ : UA E n → ℂ) : Submodule ℂ (UA E n → ℂ) := Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)

theorem RU_mem_X (φ : UA E n → ℂ) (x : infU E n) {ξ : UA E n → ℂ} (h : ξ ∈ X φ) : RU E n x ξ ∈ X φ := by
  have : X φ ≤ (X φ).comap (RU E n x) := Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    exact Submodule.subset_span ⟨x * k, (RU_RU _ _ _).symm⟩)
  exact this h

theorem self_mem_X (φ : UA E n → ℂ) : φ ∈ X φ :=
  Submodule.subset_span ⟨1, by show RU E n 1 φ = φ; rw [map_one]; rfl⟩

def rhoX (φ : UA E n → ℂ) (x : infU E n) : Module.End ℂ (X φ) :=
  (RU E n x).restrict fun _ h => RU_mem_X φ x h

theorem rhoX_mul (φ : UA E n → ℂ) (x y : infU E n) : rhoX φ (x * y) = rhoX φ x * rhoX φ y :=
  LinearMap.ext fun ξ => Subtype.ext (RU_RU (x : UA E n) y ξ.1).symm

def coef (φ : UA E n → ℂ) : Module.Dual ℂ (Module.End ℂ (X φ)) →ₗ[ℂ] (infU E n → ℂ) :=
  LinearMap.pi fun x => LinearMap.applyₗ (rhoX φ x)

def C (φ : UA E n → ℂ) : Submodule ℂ (infU E n → ℂ) := LinearMap.range (coef φ)

theorem mem_C (φ : UA E n → ℂ) (f : X φ →ₗ[ℂ] ℂ) (ξ : X φ) : (fun x : infU E n => f (rhoX φ x ξ)) ∈ C φ :=
  ⟨f ∘ₗ LinearMap.applyₗ ξ, rfl⟩

theorem C_right (φ : UA E n → ℂ) {c : infU E n → ℂ} (hc : c ∈ C φ) (y : infU E n) :
    (fun x => c (x * y)) ∈ C φ := by
  obtain ⟨B, rfl⟩ := hc
  refine ⟨B ∘ₗ LinearMap.mulRight ℂ (rhoX φ y), funext fun x => ?_⟩
  change B (rhoX φ x * rhoX φ y) = B (rhoX φ (x * y))
  rw [rhoX_mul]

def Y (φ : UA E n → ℂ) : Submodule ℂ (UA E n → ℂ) :=
  ⨅ g : UA E n, (C φ).comap (LinearMap.funLeft ℂ ℂ fun x : infU E n => g * (x : UA E n))

theorem mem_Y {φ ψ : UA E n → ℂ} : ψ ∈ Y φ ↔ ∀ g : UA E n, (fun x : infU E n => ψ (g * x)) ∈ C φ := by
  simp only [Y, Submodule.mem_iInf, Submodule.mem_comap]
  rfl

theorem le_Y (π : AutSub E n) {φ : UA E n → ℂ} (hφ : φ ∈ π.V) (h0 : φ ≠ 0) : π.V ≤ Y φ := by
  have hφY : φ ∈ Y φ := mem_Y.2 fun g =>
    mem_C φ ((LinearMap.proj g) ∘ₗ (X φ).subtype) ⟨φ, self_mem_X φ⟩
  have hst : ∀ x, ∀ ψ ∈ π.V ⊓ Y φ, RU E n x ψ ∈ π.V ⊓ Y φ := by
    intro x ψ hψ
    refine ⟨π.isAut.stable x ψ hψ.1, mem_Y.2 fun g => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_fin_mul_inf x
    have e : (fun z : infU E n => RU E n (a * b) ψ (g * z)) = fun z => ψ ((g * a) * ((z * ⟨b, hb⟩ : infU E n) : UA E n)) := by
      funext z
      rw [RU_apply, Subgroup.coe_mul, Subgroup.coe_mk, ← mul_assoc, mul_assoc g, ← fin_mul_inf ha z.2, ← mul_assoc, mul_assoc (g * a)]
    rw [e]
    exact C_right φ (mem_Y.1 hψ.2 (g * a)) ⟨b, hb⟩
  rcases π.isAut.irred (π.V ⊓ Y φ) inf_le_left hst with h | h
  · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ (⟨hφ, hφY⟩ : φ ∈ π.V ⊓ Y φ))) h0
  · rw [← h]
    exact inf_le_right

theorem eq_zero_of_vanish {K : Subgroup (finU (E := E) (n := n))} {S : Finset (UA E n)}
    (hS : ∀ g : UA E n, ∃ γ ∈ ratU E n, ∃ s ∈ S, ∃ x ∈ infU E n, ∃ k ∈ K, g = γ * s * x * (k : UA E n))
    {f : UA E n → ℂ} (hl : ∀ γ ∈ ratU E n, ∀ g, f (γ * g) = f g) (hK : ∀ k ∈ K, RU E n k f = f)
    (h0 : ∀ s ∈ S, ∀ x ∈ infU E n, f (s * x) = 0) : f = 0 := by
  funext g
  obtain ⟨γ, hγ, s, hs, x, hx, k, hk, rfl⟩ := hS g
  rw [mul_assoc, mul_assoc, hl γ hγ, ← mul_assoc]
  have := congrFun (hK k hk) (s * x)
  rw [RU_apply] at this
  rw [this, h0 s hs x hx]
  rfl

theorem exists_ne_zero (π : AutSub E n) : ∃ φ ∈ π.V, φ ≠ 0 := Submodule.exists_mem_ne_zero_of_ne_bot π.isAut.ne_bot

theorem finiteDimensional_fixed (π : AutSub E n) (K : Subgroup (finU (E := E) (n := n))) (hK : IsOpen (K : Set (finU (E := E) (n := n)))) :
    FiniteDimensional ℂ (fixed (π.rep.comp (finU (E := E) (n := n)).subtype) K) := by
  obtain ⟨φ, hφ, h0⟩ := exists_ne_zero π
  have : FiniteDimensional ℂ (X φ) := (π.isAut.aut φ hφ).kfin
  have : FiniteDimensional ℂ (C φ) := LinearMap.finiteDimensional_range _
  obtain ⟨S, hS⟩ := GlobalTheory.T.definiteUnitary_classSet_finite E n K hK
  let L : fixed (π.rep.comp (finU (E := E) (n := n)).subtype) K →ₗ[ℂ] (S → C φ) :=
    LinearMap.pi fun s => LinearMap.codRestrict (C φ)
      ((LinearMap.funLeft ℂ ℂ fun x : infU E n => (s : UA E n) * x) ∘ₗ π.V.subtype ∘ₗ (fixed _ K).subtype)
      (fun ψ => mem_Y.1 (le_Y π hφ h0 ψ.1.2) s)
  refine Module.Finite.of_injective L (LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 fun ψ hψ => ?_))
  have hK' : ∀ k ∈ K, RU E n k ψ.1.1 = ψ.1.1 := fun k hk => by
    have e : (π.rep.comp (finU (E := E) (n := n)).subtype) k ψ.1 = (((1 : K →* ℂˣ) ⟨k, hk⟩ : ℂˣ) : ℂ) • ψ.1 := ψ.2 ⟨k, hk⟩
    rw [MonoidHom.one_apply, Units.val_one, one_smul] at e
    exact congrArg Subtype.val e
  have hf := eq_zero_of_vanish hS (π.isAut.aut _ ψ.1.2).left hK' fun s hs x hx =>
    congrFun (congrArg Subtype.val (congrFun hψ ⟨s, hs⟩)) ⟨x, hx⟩
  exact Subtype.ext (Subtype.ext hf)

def stab (φ : UA E n → ℂ) : Subgroup (finU (E := E) (n := n)) where
  carrier := {k | RU E n k φ = φ}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [Subgroup.coe_mul, ← RU_RU, hb, ha]
  one_mem' := by
    show RU E n 1 φ = φ
    rw [map_one]
    rfl
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← ha]
    rw [RU_RU, InvMemClass.coe_inv, inv_mul_cancel, map_one]
    rfl

theorem finiteDimensional_hom (π : AutSub E n) : FiniteDimensional ℂ (π.rep.IntertwiningMap (autRep E n)) := by
  obtain ⟨φ, hφ, h0⟩ := exists_ne_zero π
  have : FiniteDimensional ℂ (X φ) := (π.isAut.aut φ hφ).kfin
  have : FiniteDimensional ℂ (C φ) := LinearMap.finiteDimensional_range _
  obtain ⟨S, hS⟩ := GlobalTheory.T.definiteUnitary_classSet_finite E n (stab φ) (π.isAut.aut φ hφ).level
  let φV : π.V := ⟨φ, hφ⟩
  have hXV : X φ ≤ π.V := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact π.isAut.stable _ φ hφ)
  have hmem : ∀ (T : π.rep.IntertwiningMap (autRep E n)) (s : UA E n),
      (fun x : infU E n => (T φV).1 (s * x)) ∈ C φ := by
    intro T s
    have e : (fun x : infU E n => (T φV).1 (s * x)) = fun x => ((LinearMap.proj s) ∘ₗ (autU E n).subtype ∘ₗ
        T.toLinearMap ∘ₗ Submodule.inclusion hXV) (rhoX φ x ⟨φ, self_mem_X φ⟩) :=
      funext fun x => (congrFun (congrArg Subtype.val (LinearMap.congr_fun (T.isIntertwining' (x : UA E n)) φV)) s).symm
    rw [e]
    exact mem_C φ _ _
  let Φ : π.rep.IntertwiningMap (autRep E n) →ₗ[ℂ] (S → C φ) :=
    { toFun := fun T s => ⟨fun x : infU E n => (T φV).1 ((s : UA E n) * x), hmem T s⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective Φ (LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 fun T hT => ?_))
  have hK : ∀ k ∈ stab φ, RU E n k (T φV).1 = (T φV).1 := fun k hk => by
    have e : T (π.rep k φV) = autRep E n k (T φV) := LinearMap.congr_fun (T.isIntertwining' (k : UA E n)) φV
    rw [show π.rep k φV = φV from Subtype.ext hk] at e
    exact (congrArg Subtype.val e).symm
  have hTφ : T φV = 0 := Subtype.ext (eq_zero_of_vanish hS (mem_autU.1 (T φV).2).left hK fun s hs x hx =>
    congrFun (congrArg Subtype.val (congrFun hT ⟨s, hs⟩)) ⟨x, hx⟩)
  let W : Submodule ℂ (UA E n → ℂ) := (LinearMap.ker T.toLinearMap).map π.V.subtype
  have hst : ∀ x, ∀ ψ ∈ W, RU E n x ψ ∈ W := by
    rintro x _ ⟨ψ', hψ', rfl⟩
    refine ⟨π.rep x ψ', ?_, rfl⟩
    have h1 : T ψ' = 0 := hψ'
    change T (π.rep x ψ') = 0
    have h2 : T (π.rep x ψ') = autRep E n x (T ψ') := LinearMap.congr_fun (T.isIntertwining' x) ψ'
    rw [h2, h1, map_zero]
  rcases π.isAut.irred W (Submodule.map_subtype_le _ _) hst with h | h
  · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ (⟨φV, hTφ, rfl⟩ : φ ∈ W))) h0
  · refine DFunLike.ext _ _ fun ψ => ?_
    obtain ⟨ψ', hψ', e⟩ : ψ.1 ∈ W := h.symm ▸ ψ.2
    rw [← Subtype.ext e]
    exact hψ'

theorem admissible_finiteMult : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n),
    (∀ K : Subgroup (finU (E := E) (n := n)), IsOpen (K : Set (finU (E := E) (n := n))) →
      FiniteDimensional ℂ (fixed (π.rep.comp (finU (E := E) (n := n)).subtype) K)) ∧
    FiniteDimensional ℂ (π.rep.IntertwiningMap (autRep E n)) :=
  fun _ _ _ _ _ π => ⟨fun K hK => finiteDimensional_fixed π K hK, finiteDimensional_hom π⟩

end GlobalTheory.DefU.admitted
end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem.Fld

namespace GlobalTheory.UnramInRay

theorem isModulus_of_top {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {χ : (L ≃ₐ[K] L) →* ℂˣ} (h : IsModulus L χ ⊤) {𝔪 : Ideal (𝓞 K)} (hm : 𝔪 ≠ ⊥) : IsModulus L χ 𝔪 := by
  refine ⟨hm, fun 𝔭 _ => h.2.1 𝔭 fun hd => 𝔭.isPrime.ne_top (top_le_iff.1 (Ideal.le_of_dvd hd)), ?_⟩
  rintro α β ⟨ha, hb, -, -, -, hpos⟩
  have hc : ∀ I : Ideal (𝓞 K), IsCoprime I ⊤ := fun I => Ideal.isCoprime_iff_sup_eq.2 (sup_top_eq I)
  exact h.2.2 α β ⟨ha, hb, hc _, hc _, Submodule.mem_top, hpos⟩

theorem nonempty_algHom_rayField : GlobalArtinReciprocity → ∀ (K L R : Type) [Field K] [NumberField K]
    [_root_.NumberField.IsTotallyComplex K] [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] [Field R] [NumberField R]
    [Algebra K R] (𝔪 : Ideal (𝓞 K)), 𝔪 ≠ ⊥ → IsRayField K R 𝔪 →
    (∀ 𝔭 : HeightOneSpectrum (𝓞 K), UnramIn L 𝔭) → Nonempty (L →ₐ[K] R) := by
  intro H K L R _ _ _ _ _ _ _ _ _ _ 𝔪 hm hR hL
  have := hR.1
  exact rayClassFieldMaximalSt_holds K R L 𝔪 hm hR.2 fun χ =>
    isModulus_of_top (GlobalTheory.UnramModulus.isModulus_top H K L hL χ) hm

end GlobalTheory.UnramInRay

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2



theorem laws_all : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R), FOk emb σ → ∀ (hI : I.Ok), J.Ok → ∀ (Q : PerIn I) (hQ : Q.Ok) (Pl : Rows.Places K), J.Laws emb σ hc ∧ FmLaws J Q emb σ hc Pl hI hQ := by
  intro E K ι _ _ _ _ _ _ _ R I J emb σ hc hF hI hJ Q hQ Pl
  have hd := GlobalTheory.T.levelPrimeDiamond_representation I J emb σ hc hF hI hJ
  have hfam : ∀ i, ((I.S i).fam emb (lamT hc i)).Ok := fun i => GlobalTheory.T.hermitianLatticeChartFamily_fam_ok (I.S i) emb σ (lamT hc i) hF (hI.step i)
  have hfamP : (Q.S'.fam emb Q.sgT).Ok := GlobalTheory.T.hermitianLatticeChartFamily_fam_ok Q.S' emb σ Q.sgT hF hQ.step
  refine ⟨⟨hd.1, hd.2, GlobalTheory.T.complexForms_finiteDimensional (I.S 0) emb σ (lamT hc 0) hF (hI.step 0), GlobalTheory.T.levelPrimeDiamond_preserves_complexForms I J emb σ hc hF hI hJ⟩, ?_⟩
  exact
    { fam := hfam
      famP := hfamP
      lev := fun i => GlobalTheory.T.tDat_laws_of_ok (J.A i) J.T (hI.step i) (hJ.lev i)
      good := fun i => GlobalTheory.T.weight_law_good_of_field_embedding (I.S i) emb σ (lamT hc i) hF (hI.step i) _
      basis := fun i => GlobalTheory.T.hermitianLatticeChartFamily_lawBasis (I.S i) emb σ (lamT hc i) hF (hI.step i) _
      norm := fun i => letI := I.clFin hI i; GlobalTheory.T.lawNorm_classSum_fock (I.S i) emb σ (lamT hc i) hF (hI.step i) _
      goodP := GlobalTheory.T.weight_law_good_of_field_embedding Q.S' emb σ Q.sgT hF hQ.step _
      basisP := GlobalTheory.T.hermitianLatticeChartFamily_lawBasis Q.S' emb σ Q.sgT hF hQ.step _
      normP := letI := Q.clFin hQ; GlobalTheory.T.lawNorm_classSum_fock Q.S' emb σ Q.sgT hF hQ.step _
      dia_lat := GlobalTheory.T.levelPrimeDiamond_preserves_integralForms I J emb σ hc hF hI hJ _
      B_span := fun i w P => GlobalTheory.T.local_lattice_span_at_place I J emb σ hc hF hI hJ Pl i _ w P }

end GlobalTheory.Mem.Col2
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
open Formalism.IndefR.Mult

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.LowRes

theorem multW_lowRes_inj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (i : Fin D.R.m), ∀ w ∈ (y.L F.lv2).MultW i, w ∘ₗ (y.L F.lv2).embK i = 0 → w = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG _ _ hP _ y i w hw hK
  have hM := hP.char.base.models
  set M := R.MW i (sg0 D A3.A)
  let w' : (⨂[ℂ] τ, M.sm τ) →ₗ[ℂ] (GA D (Wc D i) → ℂ) := w
  let U : MMap M := PiTensorProduct.lift.symm w'
  have hU : U ∈ Mult R.θ M _ _ := (Mult.mem_multT _ _ _ _ w').1 hw
  have h0 : U = 0 :=
    GlobalTheory.LowTypeDetermined.eq_zero_of_lowT D _ _ M R.θ hM.inf
      (GlobalTheory.LowTypeRestriction.lowT_ne_bot _) _ _ U hU (fun v => by
        have e := LinearMap.congr_fun hK (PiTensorProduct.tprod ℂ v)
        have e2 : w' (PiTensorProduct.map (fun τ => (lowT M τ).subtype) (PiTensorProduct.tprod ℂ v)) = 0 := e
        rw [PiTensorProduct.map_tprod] at e2
        have e3 : PiTensorProduct.lift U (PiTensorProduct.tprod ℂ (fun τ => (lowT M τ).subtype (v τ))) = 0 := by
          rw [show PiTensorProduct.lift U = w' from LinearEquiv.apply_symm_apply _ w']; exact e2
        rw [PiTensorProduct.lift.tprod] at e3
        exact e3)
  have hUw : PiTensorProduct.lift U = w' := LinearEquiv.apply_symm_apply _ w'
  show w' = 0
  rw [← hUw, h0, map_zero]

end GlobalTheory.Mem.R3.Rw.LowRes

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

theorem _root_.GlobalTheory.T.complexSpan_rationalLiftForms_eq_basePart : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (i : Fin D.R.m) (p : A3.fam3.base3.Ix), Submodule.span ℂ ((Z.jW i) '' ((s0Of R F).Wp i p : Set (Fin ((s0Of R F).dW i) → D.what₂.LL))) = (R.Wp3 i p).comap (Y.mj.eW i) := by
  first | exact @GlobalTheory.Mem.R3.RatSpan.span_jW_wp | exact GlobalTheory.Mem.R3.RatSpan.span_jW_wp | (intros; apply GlobalTheory.Mem.R3.RatSpan.span_jW_wp <;> assumption)
end

section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

theorem _root_.GlobalTheory.T.classPair_moved_of_multipliesLocalFunctional : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (P : LvTied u A i hi) (K : ClsTied u i hi) (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v), FvTie P K fMe → ∀ (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (γ : GL (Fin (D.R.N i)) D.host.E) (a : ℤ), MulsF K.lev (A.eV v).1 (A.eV v).2 a (mov K (A.eV v).1 c γ c') → (pc P v c').act (glE γ) = (pc P v c).dil (a : (D.mem u).A.Fv v) := by
  first | exact @GlobalTheory.LevelHecke.MovePair.pc_act_of_mulsF | exact GlobalTheory.LevelHecke.MovePair.pc_act_of_mulsF | (intros; apply GlobalTheory.LevelHecke.MovePair.pc_act_of_mulsF <;> assumption)
end
