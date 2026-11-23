module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle239
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle240
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle242
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle248
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle249
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle241
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle236
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle231
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle152
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle155
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemXSmulOfProjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle188
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle243
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachSaturationQPowerMemFrobeniusSpan
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

theorem _root_.GlobalTheory.T.prod_other_root_factors_action_first_coordinate : ∀ {O : Type} [CommRing O] [IsDomain O] {n r t : ℕ} (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O))) (E X₀ : Matrix (Fin n) (Fin n) O) (ρ : ℕ → O), 2 ≤ t → (∀ u, e ((E.map (toFr O)).mulVec u) = (0, (e u).2)) → (∀ u, e ((X₀.map (toFr O)).mulVec u) = (0, fun c : Fin t => toFr O (ρ ((c : ℕ) + 1)) * (e u).2 c)) → ∀ u, e (((((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • E).prod).map (toFr O)).mulVec u) = (0, fun c : Fin t => if (c : ℕ) = 0 then toFr O (∏ c' ∈ Finset.Ioc 1 t, (ρ 1 - ρ c')) * (e u).2 c else 0) := by
  first | exact @GlobalTheory.RootFactorProduct.prod_other_factors_action | exact GlobalTheory.RootFactorProduct.prod_other_factors_action | (intros; apply GlobalTheory.RootFactorProduct.prod_other_factors_action <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

theorem _root_.GlobalTheory.T.exists_block_action_of_decomposition : ∀ {Γ X O : Type} [Group Γ] [CommRing O] [IsDomain O] {n r t : ℕ} (T : Subalgebra O (X → O)) (rep : X → (Γ →* GL (Fin n) O)) (ρ : Γ →* GL (Fin r) O) (χ : ℕ → (Γ →* Oˣ)) (π : X) (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O))), Submodule.span O (Set.range (mat ρ)) = ⊤ → IsDecomp (t := t) (rep π) ρ χ e → ∃ (ψρ : (X → Matrix (Fin n) (Fin n) O) → Matrix (Fin r) (Fin r) O) (ψχ : Fin t → (X → Matrix (Fin n) (Fin n) O) → O), (∀ a, InRing T rep a → ∀ u, e (((a π).map (toFr O)).mulVec u) = (((ψρ a).map (toFr O)).mulVec (e u).1, fun c : Fin t => toFr O (ψχ c a) * (e u).2 c)) ∧ ∀ P : Matrix (Fin r) (Fin r) O, ∃ a, InRing T rep a ∧ ψρ a = P := by
  first | exact @GlobalTheory.SpanBlockAction.exists_block_action | exact GlobalTheory.SpanBlockAction.exists_block_action | (intros; apply GlobalTheory.SpanBlockAction.exists_block_action <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.truncatedWhittaker_weilRep_eventually : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (m : A.Meas ψ) (x : A.Kˣ) (γ : ℂ) W, A.IsWeil ψ x A.etaK (m.μL x) γ W → ∀ φ, IsTest φ → ∀ a : A.K, IsUnit a → (∀ y : A.L, IsUnit y → a = x * A.NL y → ∀ᶠ c in 𝓝[≠] (0 : F), A.abelian₂ m.μK ψ a (fun g => W g φ 0) c = γ * A.orbL m.ν φ y) ∧ ((¬ ∃ y : A.L, IsUnit y ∧ a = x * A.NL y) → ∀ᶠ c in 𝓝[≠] (0 : F), A.abelian₂ m.μK ψ a (fun g => W g φ 0) c = 0) := by
  first | exact @GlobalTheory.JR.WhitX.lam_weil_eventually | exact GlobalTheory.JR.WhitX.lam_weil_eventually | (intros; apply GlobalTheory.JR.WhitX.lam_weil_eventually <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_weilRepSL2_glBorderedBlock : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∃ W : SpecialLinearGroup (Fin 2) F → (Gl r F → ℂ) → Gl r F → ℂ, IsTestRep W ∧ ∀ f, IsTest f → (∀ t Y, W (nS t) f Y = ψ (t * mom Y 0) * f Y) ∧ W (wS F) f = fourG M ψ f := by
  first | exact @GlobalTheory.JR.weil_repG | exact GlobalTheory.JR.weil_repG | (intros; apply GlobalTheory.JR.weil_repG <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_weilRepresentation_hyperbolic_split : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → IsField A.K → ¬ IsField A.L → ∀ (x : A.Kˣ) (μ : Measure A.L), SelfDual μ (A.kerL ψ x) → ∃ W, A.IsWeil ψ x A.etaK μ 1 W := by
  first | exact @GlobalTheory.JR.weil_hyperbolic | exact GlobalTheory.JR.weil_hyperbolic | (intros; apply GlobalTheory.JR.weil_hyperbolic <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.kirillov_vanishing_of_limit : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ Ψ, A.InI Ψ → (∀ a : A.K, IsUnit a → Tendsto (A.abelian₂ μK ψ a Ψ) (𝓝[≠] 0) (𝓝 0)) → (∀ z, Ψ (wS A.K * nS z) = 0) ∧ ∀ (a : A.K) (c : F), A.abelian₂ μK ψ a (fun h => Ψ (h * wS A.K)) c = 0 := by
  first | exact @GlobalTheory.JR.kirillov_vanishing_l2 | exact GlobalTheory.JR.kirillov_vanishing_l2 | (intros; apply GlobalTheory.JR.kirillov_vanishing_l2 <;> assumption)
end

section

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.Isog

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem latHom_ext {T T' : LocLat G Qp LL O} {u w : LatHom T.L T'.L} (h : u.f = w.f) : u = w := by
  cases u; cases w; cases h; rfl

theorem exists_quasi_inverse (c : O)
    (hc : ∀ a : LL, ∃ (k : ℕ) (b : O), algebraMap O LL b = algebraMap O LL c ^ k * a)
    {T' T : LocLat G Qp LL O} (f : LatHom T'.L T.L) (hf : Function.Bijective f.f) :
    ∃ (m : ℕ) (g : LatHom T.L T'.L), latComp g f = latSmul T' (c ^ m) ∧
      latComp f g = latSmul T (c ^ m) := by
  let e : T'.V ≃ₗ[LL] T.V := LinearEquiv.ofBijective f.f hf
  have he : ∀ g y, e.symm (T.ρ g y) = T'.ρ g (e.symm y) := by
    intro g y
    apply e.injective
    rw [e.apply_symm_apply]
    have := f.equiv g (e.symm y)
    change e _ = T.ρ g (e _) at this
    rw [this, e.apply_symm_apply]
  obtain ⟨m, hm⟩ := GlobalTheory.WachSat.exists_pow_smul_le (LL := LL) c hc T'.L.T
    (T.L.T.map (e.symm.toLinearMap.restrictScalars O)) T'.L.span (T.L.fg.map _)
  haveI : ContinuousSMul LL T'.V := IsModuleTopology.toContinuousSMul LL T'.V
  let g : LatHom T.L T'.L :=
    { f := algebraMap O LL (c ^ m) • e.symm.toLinearMap
      equiv := fun g y => by simp [he]
      cont := IsModuleTopology.continuous_of_linearMap _
      T_le := fun y hy => by
        have := hm _ (Submodule.mem_map_of_mem hy)
        rw [← algebraMap_smul LL] at this
        exact this }
  refine ⟨m, g, latHom_ext ?_, latHom_ext ?_⟩
  · ext y
    change algebraMap O LL (c ^ m) • e.symm (e y) = algebraMap O LL (c ^ m) • y
    rw [e.symm_apply_apply]
  · ext y
    change e (algebraMap O LL (c ^ m) • e.symm y) = algebraMap O LL (c ^ m) • y
    rw [map_smul, e.apply_symm_apply]

variable (W : LocWach PD LL O v n)

theorem dd_torsionFree (hp : ∀ a : O, (PD.p : O) * a = 0 → a = 0) (T : LocLat G Qp LL O) (m : ℕ)
    (x : W.DD T) (hx : ((PD.p : O) ^ m) • x = 0) : x = 0 := by
  have hreg : ∀ (k : ℕ) (y : W.EE), (PD.p : W.EE) ^ k * y = 0 → y = 0 := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      exact ih y (GlobalTheory.WachSat.ee_torsionFree W hp _ (by rw [← hy]; ring))
  haveI := (W.DD_free T).1
  let b := Module.Free.chooseBasis W.EE (W.DD T)
  rw [← algebraMap_smul W.EE, map_pow, map_natCast] at hx
  apply b.repr.injective
  ext j
  have := congrArg (fun z => b.repr z j) hx
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply] at this
  simpa using hreg m _ this

theorem globalBasis_of_basis (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ)
    (b : Module.Basis (Fin (Module.finrank O ↥T.L.T)) (LetA O n) ↥(W.N T)) :
    GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.GlobalBasis W T := by
  let b' := (W.N_base T hT).basis b
  have hb : (fun j => (b j : W.DD T)) = b' := by
    funext j
    exact ((W.N_base T hT).basis_apply b j).symm
  refine ⟨b, ?_, ?_⟩
  · rw [hb]; exact b'.linearIndependent
  · rw [hb]; exact b'.span_eq

theorem isog_generic (hp : ∀ a : O, (PD.p : O) * a = 0 → a = 0)
    (hc : ∀ a : LL, ∃ (k : ℕ) (b : O), algebraMap O LL b = algebraMap O LL (PD.p : O) ^ k * a)
    (T' T : LocLat G Qp LL O) (f : LatHom T'.L T.L) (hT' : IsCrys PD T'.ρ) (hT : IsCrys PD T.ρ)
    (hs : ∀ (m : ℕ) (x : W.DD T'), ((PD.p : O) ^ m) • x ∈ W.N T' → x ∈ W.N T')
    (hf : Function.Bijective f.f) :
    Function.Injective (W.map f) ∧
    (∃ c : ℕ, ∀ y : W.DD T, ∃ x : W.DD T', W.map f x = ((PD.p : O) ^ c) • y ∧
      (y ∈ W.N T → x ∈ W.N T')) ∧
    ∀ x : W.DD T', W.map f x ∈ W.N T ↔ x ∈ W.N T' := by
  obtain ⟨m, g, hgf, hfg⟩ := exists_quasi_inverse (PD.p : O) hc f hf
  have h1 : ∀ x, W.map g (W.map f x) = ((PD.p : O) ^ m) • x := fun x => by
    rw [← W.map_comp, hgf, W.map_latSmul]
  have h2 : ∀ x, W.map f (W.map g x) = ((PD.p : O) ^ m) • x := fun x => by
    rw [← W.map_comp, hfg, W.map_latSmul]
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_,
    ⟨m, fun y => ⟨W.map g y, h2 y, W.map_N g hT hT' y⟩⟩,
    fun x => ⟨fun hx => hs m x ?_, W.map_N f hT' hT x⟩⟩
  · refine dd_torsionFree W hp T' m x ?_
    rw [← h1, hx, map_zero]
  · rw [← h1]
    exact W.map_N g hT hT' _ hx

end Generic

section Loc

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l)

theorem p_regular (a : ↥(OL LL)) (ha : (((P.PD K).p : ℕ) : ↥(OL LL)) * a = 0) : a = 0 := by
  have hl0 : (l : ↥LL.1) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  rw [P.PD_p] at ha
  have : (l : ↥LL.1) * (a : ↥LL.1) = 0 := by
    have := congrArg (Subtype.val) ha
    simpa using this
  exact Subtype.ext ((mul_eq_zero.1 this).resolve_left hl0)

theorem exists_pow_mul_integral (a : ↥LL.1) : ∃ (k : ℕ) (b : ↥(OL LL)), algebraMap ↥(OL LL) ↥LL.1 b =
    algebraMap ↥(OL LL) ↥LL.1 (((P.PD K).p : ℕ) : ↥(OL LL)) ^ k * a := by
  rw [P.PD_p]
  have : ∃ k : ℕ, 0 ≤ P.v LL ((l : ↥LL.1) ^ k * a) := by
    cases hq : P.v LL a with
    | top => exact ⟨0, by simp [hq]⟩
    | coe q =>
      obtain ⟨k, hk⟩ := exists_nat_ge (-q)
      refine ⟨k, ?_⟩
      rw [AddValuation.map_mul, AddValuation.map_pow, P.v_l, hq, nsmul_one, ← WithTop.coe_natCast,
        ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe]
      linarith
  obtain ⟨k, hk⟩ := this
  exact ⟨k, ⟨_, (P.v_O LL _).1 hk⟩, by rw [map_natCast]; rfl⟩

end Loc

section Main

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL)

set_option synthInstance.maxHeartbeats 100000 in
theorem sat_loc (T : Lt K LL) (hT : IsCrys (P.PD K) T.ρ) (m : ℕ) (x : (H.W K s LL h).DD T)
    (hx : ((((P.PD K).p : ℕ) : ↥(OL LL)) ^ m) • x ∈ (H.W K s LL h).N T) : x ∈ (H.W K s LL h).N T := by
  obtain ⟨b⟩ := N_basis_loc H K s LL h T hT
  exact GlobalTheory.WachSat.mem_of_pow_smul_mem _ (p_regular P K LL) T (globalBasis_of_basis _ T hT b) m x hx

theorem isog_loc (T' T : Lt K LL) (f : LatHom T'.L T.L) (hT' : IsCrys (P.PD K) T'.ρ)
    (hT : IsCrys (P.PD K) T.ρ) (hf : Function.Bijective f.f) :
    Function.Injective ((H.W K s LL h).map f) ∧
    (∃ c : ℕ, ∀ y : (H.W K s LL h).DD T, ∃ x : (H.W K s LL h).DD T',
      (H.W K s LL h).map f x = ((((P.PD K).p : ℕ) : ↥(OL LL)) ^ c) • y ∧
      (y ∈ (H.W K s LL h).N T → x ∈ (H.W K s LL h).N T')) ∧
    ∀ x : (H.W K s LL h).DD T', (H.W K s LL h).map f x ∈ (H.W K s LL h).N T ↔
      x ∈ (H.W K s LL h).N T' :=
  isog_generic (H.W K s LL h) (p_regular P K LL) (exists_pow_mul_integral P K LL) T' T f hT' hT
    (sat_loc H K s LL h T' hT') hf

end Main

end GlobalTheory.NL.Isog
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.SatFree

theorem isBaseChange_between (A E : Type) [CommRing A] [CommRing E] [Algebra A E]
    [Module.Flat A E] (D₁ D₂ : Type) [AddCommGroup D₁] [AddCommGroup D₂]
    [Module E D₁] [Module E D₂] [Module A D₁] [Module A D₂]
    [IsScalarTower A E D₁] [IsScalarTower A E D₂]
    (q : D₁ →ₗ[E] D₂) (hq : Function.Surjective q) (N₁ : Submodule A D₁) (N₂ : Submodule A D₂)
    (h₁ : IsBaseChange E N₁.subtype) (h₂ : IsBaseChange E N₂.subtype)
    (S : Submodule A D₂) (hS : S ≤ N₂) (hqS : ∀ x ∈ N₁, q x ∈ S) :
    IsBaseChange E S.subtype := by
  let i : S →ₗ[A] N₂ := Submodule.inclusion hS
  have hi : Function.Injective i := Submodule.inclusion_injective hS
  have hiT : Function.Injective (LinearMap.lTensor E i) :=
    Module.Flat.lTensor_preserves_injective_linearMap i hi
  let Φ : E ⊗[A] S →ₗ[E] D₂ := S.subtype.liftBaseChange E
  have hcomm : ∀ t : E ⊗[A] S, Φ t = h₂.equiv (LinearMap.lTensor E i t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [Φ, IsBaseChange.equiv_tmul, i]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hΦi : Function.Injective Φ := by
    intro s t hst
    apply hiT
    apply h₂.equiv.injective
    rw [← hcomm, ← hcomm, hst]
  have hΦs : Function.Surjective Φ := by
    intro d
    obtain ⟨x, rfl⟩ := hq d
    have : q x ∈ LinearMap.range Φ := by
      refine h₁.inductionOn x ?_ ?_ ?_
      · intro m
        refine ⟨1 ⊗ₜ ⟨q m, hqS m m.2⟩, ?_⟩
        simp [Φ, LinearMap.liftBaseChange_tmul]
      · intro e y hy
        rw [map_smul]
        exact (LinearMap.range Φ).smul_mem e hy
      · intro a b ha hb
        rw [map_add (f := _)]
        exact (LinearMap.range Φ).add_mem ha hb
    exact this
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective Φ ⟨hΦi, hΦs⟩) ?_
  intro x
  show Φ (1 ⊗ₜ x) = x
  simp [Φ, LinearMap.liftBaseChange_tmul]

theorem freeA_of_basis {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp]
    [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (S : Submodule (LetA O n) (W.DD T)) {r : ℕ}
    (b : Module.Basis (Fin r) (LetA O n) S) : FreeA W T S := by
  refine ⟨r, fun j => (b j : W.DD T), fun j => (b j).2, fun x hx => ?_⟩
  refine ⟨b.equivFun ⟨x, hx⟩, ?_, ?_⟩
  · have h2 : ((⟨x, hx⟩ : S) : W.DD T) = ((∑ j, b.equivFun ⟨x, hx⟩ j • b j : S) : W.DD T) := by
      rw [b.sum_equivFun]
    rw [Submodule.coe_sum] at h2
    simpa only [Submodule.coe_smul] using h2
  · intro a ha
    have : (⟨x, hx⟩ : S) = ∑ j, a j • b j := by
      apply Subtype.ext
      simpa using ha
    rw [this, ← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

end GlobalTheory.NL.SatFree

namespace GlobalTheory.NL.SatFree



theorem satM_free_loc {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K : FinExt l)
    (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T₁ T₂ : Lt K LL) (π : LatHom T₁.L T₂.L)
    (c1 : IsCrys (P.PD K) T₁.ρ) (c2 : IsCrys (P.PD K) T₂.ρ)
    (hsurj : Function.Surjective ((H.W K s LL h).map π))
    (hflat : Module.Flat (AA K LL) (H.W K s LL h).EE) :
    FreeA (H.W K s LL h) T₂ (GlobalTheory.NL.Coker.satM l (((H.W K s LL h).N T₁).map (mapA (H.W K s LL h) π))
      ((H.W K s LL h).N T₂)) ∧
    IsBaseChange (H.W K s LL h).EE (GlobalTheory.NL.Coker.satM l (((H.W K s LL h).N T₁).map
      (mapA (H.W K s LL h) π)) ((H.W K s LL h).N T₂)).subtype := by
  obtain ⟨_, -, hl⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  haveI := (P.PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hproj := H.W_proj K s LL h T₂
  generalize H.W K s LL h = W at hproj hsurj hflat ⊢
  set S := GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂) with hSdef
  have hSN : S ≤ W.N T₂ := GlobalTheory.NL.Coker.satM_le _ _ _
  have hbc : IsBaseChange W.EE S.subtype := by
    refine isBaseChange_between (AA K LL) W.EE (W.DD T₁) (W.DD T₂) (W.map π) hsurj (W.N T₁) (W.N T₂)
      (W.N_base T₁ c1) (W.N_base T₂ c2) S hSN ?_
    intro x hx
    exact GlobalTheory.NL.Coker.le_satM l (fun y hy => by
      obtain ⟨z, hz, rfl⟩ := hy
      exact W.map_N π c1 c2 z hz) ⟨x, hx, rfl⟩
  refine ⟨?_, hbc⟩
  obtain ⟨hfree, hrk⟩ := W.DD_free T₂
  haveI : Module.Finite (AA K LL) ↥(W.N T₂) := Module.Finite.iff_fg.mpr (W.N_fg T₂)
  haveI hR : IsNoetherianRing (PowerSeries ↥(OL LL)) := inferInstance
  haveI hA : IsNoetherianRing (AA K LL) :=
    inferInstanceAs (IsNoetherianRing (ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → PowerSeries ↥(OL LL)))
  haveI hNn : IsNoetherian (AA K LL) ↥(W.N T₂) :=
    isNoetherian_of_isNoetherianRing_of_finite (AA K LL) ↥(W.N T₂)
  haveI : Module.Finite (AA K LL) ↥S :=
    Module.Finite.iff_fg.mpr (isNoetherian_submodule.mp hNn S hSN)
  have hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
    intro h0
    have := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h0
    simp [(Fact.out : l.Prime).ne_zero] at this
  have hreg : ∀ u v : W.DD T₂, (letπ : AA K LL) • u = (letπ : AA K LL) • v → u = v := by
    intro u v h1
    rw [← algebraMap_smul W.EE, ← algebraMap_smul W.EE (letπ : AA K LL) v] at h1
    exact W.EE_π.smul_left_cancel.mp h1
  have hlC : ((l : ℕ) : AA K LL) = fun _ => PowerSeries.C ((l : ℕ) : ↥(OL LL)) := by
    funext i
    simp
  have hX : IsSMulRegular ↥S (fun _ => PowerSeries.X : AA K LL) := by
    intro x y hxy
    exact Subtype.ext (hreg _ _ (congrArg Subtype.val hxy))
  have hC : ∀ x y : ↥S, (fun _ => PowerSeries.C ((l : ℕ) : ↥(OL LL)) : AA K LL) • x =
      (fun _ => PowerSeries.X : AA K LL) • y → ∃ z : ↥S, x = (fun _ => PowerSeries.X : AA K LL) • z := by
    intro x y hxy
    have e1 : zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) (PowerSeries.C ((l : ℕ) : ℤ_[l])) =
        fun _ => PowerSeries.C ((l : ℕ) : ↥(OL LL)) := by
      funext i
      simp
    have e2 : zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) PowerSeries.X = fun _ => PowerSeries.X := by
      funext i
      simp [zlA]
    let x' : ↥(W.N T₂) := ⟨x, hSN x.2⟩
    let y' : ↥(W.N T₂) := ⟨y, hSN y.2⟩
    have hxy' : (fun _ => PowerSeries.C ((l : ℕ) : ↥(OL LL)) : AA K LL) • x' =
        (fun _ => PowerSeries.X : AA K LL) • y' := by
      apply Subtype.ext
      change _ • (x : W.DD T₂) = _ • (y : W.DD T₂)
      exact congrArg Subtype.val hxy
    obtain ⟨z, hz⟩ := GlobalTheory.HWL.mem_smul_of_projective_comp _ hproj ((l : ℕ) : ℤ_[l])
      (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) e1 e2 x' y' hxy'
    have hzx : (letπ : AA K LL) • (z : W.DD T₂) = (x : W.DD T₂) := (congrArg Subtype.val hz).symm
    have hzy : ((l : ℕ) : AA K LL) • (z : W.DD T₂) = (y : W.DD T₂) := by
      apply hreg
      rw [smul_comm, hzx, hlC]
      exact congrArg Subtype.val hxy
    have hzS : (z : W.DD T₂) ∈ S := by
      refine GlobalTheory.NL.Coker.mem_satM_of_smul z.2 ?_ ?_
      · rw [hzy]; exact y.2
      · rw [hzx]; exact x.2
    exact ⟨⟨z, hzS⟩, Subtype.ext hzx.symm⟩
  obtain ⟨b⟩ := GlobalTheory.WachFree.basis_of_regular (ι := ZMod (Module.finrank ℚ_[l] ↥(K0 K)))
    (O := ↥(OL LL)) (N := ↥S) (E := W.EE) (D := W.DD T₂) W.EE_inj S.subtype hbc
    ((l : ℕ) : ↥(OL LL)) hl0 hl hX hC
  exact freeA_of_basis W T₂ S b

end GlobalTheory.NL.SatFree

namespace GlobalTheory.NL.SatFree

theorem satM_free_and_spans : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → Module.Flat (AA K LL) W.EE → FreeA W T₂ (GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)) ∧ IsBaseChange W.EE (GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)).subtype := by
  intro D HW F l _ K s LL h W T₀ T₁ T₂ ι π _ c1 c2 hses hflat
  have hex : Function.Injective (((HW l).W K s LL h).map ι) ∧
      Function.Exact (((HW l).W K s LL h).map ι) (((HW l).W K s LL h).map π) ∧
      Function.Surjective (((HW l).W K s LL h).map π) :=
    by
      haveI := GlobalTheory.EtaleExact.finite_OL LL
      haveI : IsNoetherianRing ↥(OL LL) := IsNoetherianRing.of_finite ℤ_[l] ↥(OL LL)
      have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
      refine GlobalTheory.EtaleExact.exact_of_tie (((F l).E K s LL h).tie)
        (GlobalTheory.EtaleExact.map_ne_top_of_tie (((F l).E K s LL h).tie) ?_ ?_) T₀ T₁ T₂ ι π hses
      · rw [hp]
        exact GlobalTheory.EtaleExact.isUnit_or_dvd_pow (D.loc l) LL
      · rw [hp]
        exact GlobalTheory.EtaleExact.sep_RW LL
  exact satM_free_loc (HW l) K s LL h T₁ T₂ π c1 c2 hex.2.2 hflat

end GlobalTheory.NL.SatFree
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.wachSaturation_frobenius_mem_up_to_Q_power : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₁ T₂ : Lt K LL) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → ∀ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂), ∃ k : ℕ, W.Q ^ k • W.φD T₂ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂) := by
  first | exact @GlobalTheory.NL.PhiSat.φD_satM_Q | exact GlobalTheory.NL.PhiSat.φD_satM_Q | (intros; apply GlobalTheory.NL.PhiSat.φD_satM_Q <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.saturation_gamma_stable_of_good : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₁ T₂ : Lt K LL) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → (∀ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂), W.γ T₂ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)) ∧ ∀ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂), W.γ T₂ x - x ∈ (GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)).map (smulA W T₂ letπ) := by
  first | exact @GlobalTheory.NL.GamSat.wachSaturation_gamma_stable_and_sub_one_mem_pi_smul | exact GlobalTheory.NL.GamSat.wachSaturation_gamma_stable_and_sub_one_mem_pi_smul | (intros; apply GlobalTheory.NL.GamSat.wachSaturation_gamma_stable_and_sub_one_mem_pi_smul <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.wachSaturation_Q_power_mem_frobenius_span : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₁ T₂ : Lt K LL) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → FreeA W T₂ (GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)) → IsBaseChange W.EE (GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)).subtype → ∀ y ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂), ∃ k : ℕ, W.Q ^ k • y ∈ φspan W T₂ (GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)) := by
  first | exact @GlobalTheory.NL.SatPhiSpan.satM_Qpow_mem_φspan | exact GlobalTheory.NL.SatPhiSpan.satM_Qpow_mem_φspan | (intros; apply GlobalTheory.NL.SatPhiSpan.satM_Qpow_mem_φspan <;> assumption)
end
