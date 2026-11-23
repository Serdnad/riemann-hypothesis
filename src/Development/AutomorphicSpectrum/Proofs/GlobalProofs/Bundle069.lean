module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle067
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle322
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle391
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle357
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemFormsOnOfMemSpan
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct Topology InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.HCCusp
open GlobalTheory.Cusp GlobalTheory.Mem.AutSpace GlobalTheory.Mem.Lift ComplexConjugate

variable {D : D7} {θ : GlobalTheory.Mem.Th.InfF D} {V : HSp D}

theorem cont_bdd (hθ : IsInfFam θ) (φ : Mc θ V) :
    Continuous (φ : GA D V → ℂ) ∧ ∃ C : ℝ, ∀ g, ‖(φ : GA D V → ℂ) g‖ ≤ C :=
  ⟨(mem_Mc_iff.1 φ.2).1.cont, GlobalTheory.CuspDecay.bounded_of_cuspForm
    (GlobalTheory.Grow.cuspRapidDecay_of_bound GlobalTheory.CuspGeo.cuspDecayBound) hθ (mem_Mc_iff.1 φ.2).1 (mem_Mc_iff.1 φ.2).2⟩

theorem integrableOn_mul_conj {μ : Measure (GA D V)} [μ.IsHaarMeasure] {𝓕 : Set (GA D V)} (hfin : μ 𝓕 ≠ ⊤)
    (hθ : IsInfFam θ) (φ ψ : Mc θ V) :
    IntegrableOn (fun g => (φ : GA D V → ℂ) g * conj ((ψ : GA D V → ℂ) g)) 𝓕 μ := by
  obtain ⟨c1, B1, h1⟩ := cont_bdd hθ φ
  obtain ⟨c2, B2, h2⟩ := cont_bdd hθ ψ
  have hc : Continuous (fun g => (φ : GA D V → ℂ) g * conj ((ψ : GA D V → ℂ) g)) :=
    c1.mul (Complex.continuous_conj.comp c2)
  refine Measure.integrableOn_of_bounded (M := B1 * B2) hfin hc.measurable.aestronglyMeasurable (.of_forall fun g => ?_)
  rw [norm_mul, RCLike.norm_conj]
  exact mul_le_mul (h1 g) (h2 g) (norm_nonneg _) ((norm_nonneg _).trans (h1 g))

theorem setIntegral_der_mul_conj {μ : Measure (GA D V)} [μ.IsHaarMeasure] {𝓕 : Set (GA D V)}
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) (hθ : IsInfFam θ) (τ : D.what₂.Tau)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (φ ψ : Mc θ V) :
    ∫ g in 𝓕, (φ : GA D V → ℂ) g * conj ((der hθ τ hX ψ : GA D V → ℂ) g) ∂μ =
      -∫ g in 𝓕, (der hθ τ hX φ : GA D V → ℂ) g * conj ((ψ : GA D V → ℂ) g) ∂μ := by
  obtain ⟨-, -, -, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hH : μ.IsHaarMeasure := inferInstance
  have hfin : μ 𝓕 ≠ ⊤ := (GlobalTheory.Mem.QuotVol.quot_volume_ne_zero_ne_top D V μ 𝓕 ⟨hH, h𝓕⟩).2
  haveI := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ hH).1
  obtain ⟨c0, B0, b0⟩ := cont_bdd hθ φ
  obtain ⟨c1, B1, b1⟩ := cont_bdd hθ ψ
  obtain ⟨c2, B2, b2⟩ := cont_bdd hθ (der hθ τ hX φ)
  obtain ⟨c3, B3, b3⟩ := cont_bdd hθ (der hθ τ hX ψ)
  have cc : ∀ {f : GA D V → ℂ}, Continuous f → Continuous fun g => conj (f g) :=
    fun h => Complex.continuous_conj.comp h
  have nn : ∀ {f : GA D V → ℂ} {B : ℝ}, (∀ g, ‖f g‖ ≤ B) → 0 ≤ B :=
    fun h => (norm_nonneg _).trans (h 1)
  have sm : ∀ (f : Mc θ V) (g : GA D V), HasDerivAt (fun t : ℝ => (f : GA D V → ℂ) (g * oneP θ V τ X t))
      (Rder θ V τ X f.1 g) 0 := fun f g => hasDerivAt_Rder (mem_Mc_iff.1 f.2).1.smooth hX g
  have key := GlobalTheory.Mem.IntByParts.setIntegral_deriv_eq_zero (GQ V) μ h𝓕 hfin
    (Φ := fun g => (φ : GA D V → ℂ) g * conj ((ψ : GA D V → ℂ) g))
    (Φ' := fun g => (der hθ τ hX φ : GA D V → ℂ) g * conj ((ψ : GA D V → ℂ) g) +
      (φ : GA D V → ℂ) g * conj ((der hθ τ hX ψ : GA D V → ℂ) g))
    (B := B0 * B1) (B' := B2 * B1 + B0 * B3)
    (fun γ hγ g => by
      simp only [(mem_Mc_iff.1 φ.2).1.left γ hγ g, (mem_Mc_iff.1 ψ.2).1.left γ hγ g])
    (c0.mul (cc c1)) ((c2.mul (cc c1)).add (c0.mul (cc c3)))
    (fun g => by
      rw [norm_mul, RCLike.norm_conj]
      exact mul_le_mul (b0 g) (b1 g) (norm_nonneg _) (nn b0))
    (fun g => by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, RCLike.norm_conj]
        exact mul_le_mul (b2 g) (b1 g) (norm_nonneg _) (nn b2)
      · rw [norm_mul, RCLike.norm_conj]
        exact mul_le_mul (b0 g) (b3 g) (norm_nonneg _) (nn b0))
    (oneP_zero (V := V) (τ := τ) (X := X) hθ)
    (fun g t => (hasDerivAt_oneP hθ hX (sm φ) g t).mul (hasDerivAt_oneP hθ hX (sm ψ) g t).star)
  rw [integral_add (integrableOn_mul_conj hfin hθ _ _) (integrableOn_mul_conj hfin hθ _ _)] at key
  exact eq_neg_of_add_eq_zero_right key

theorem inner_eq_petersson {μ : Measure (GA D V)} [μ.IsHaarMeasure] (hθ : IsInfFam θ) (φ ψ : Mc θ V) :
    ⟪io μ hθ φ, io μ hθ ψ⟫_ℂ = petersson V μ ψ.1 φ.1 :=
  petersson_inner_eq_integral_quotient _ hθ ψ φ

theorem inner_eq_setIntegral {μ : Measure (GA D V)} [μ.IsHaarMeasure] {𝓕 : Set (GA D V)}
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) (hθ : IsInfFam θ) (φ ψ : Mc θ V) :
    ⟪io μ hθ φ, io μ hθ ψ⟫_ℂ = ∫ g in 𝓕, (ψ : GA D V → ℂ) g * conj ((φ : GA D V → ℂ) g) ∂μ := by
  rw [inner_eq_petersson]
  exact petersson_eq h𝓕 (mem_Mc_iff.1 ψ.2).1.left (mem_Mc_iff.1 φ.2).1.left

theorem inner_io_der_skew : ∀ (D : D7) (θ : GlobalTheory.Mem.Th.InfF D) (hθ : IsInfFam θ) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hX : X ∈ lieAt V τ) (ψ χ : GlobalTheory.CompanionTheory.HCCusp.Mc θ V), ⟪GlobalTheory.CompanionTheory.HCCusp.io μ hθ (GlobalTheory.CompanionTheory.HCCusp.der hθ τ hX ψ), GlobalTheory.CompanionTheory.HCCusp.io μ hθ χ⟫_ℂ = -⟪GlobalTheory.CompanionTheory.HCCusp.io μ hθ ψ, GlobalTheory.CompanionTheory.HCCusp.io μ hθ (GlobalTheory.CompanionTheory.HCCusp.der hθ τ hX χ)⟫_ℂ := by
  intro D θ hθ V μ _ τ X hX ψ χ
  obtain ⟨𝓕, h𝓕⟩ := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ inferInstance).2
  rw [inner_eq_setIntegral h𝓕, inner_eq_setIntegral h𝓕]
  exact setIntegral_der_mul_conj h𝓕 hθ τ hX χ ψ

end GlobalTheory.CompanionTheory.HCCusp
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart

open GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar

section Groups

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

def ptStab (A : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E)) : Subgroup (GAd σ J) where
  carrier := {g | ∀ y ∈ A, (matHom _ σ J g).1 *ᵥ y = y}
  one_mem' := fun y _ => by simp
  mul_mem' := fun {a b} ha hb y hy => by
    rw [map_mul, Units.val_mul, ← mulVec_mulVec, hb y hy, ha y hy]
  inv_mem' := fun {a} ha y hy => by
    conv_lhs => rw [← ha y hy]
    rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec]

def block (T : Finset (Fin r)) (k : Fin r) : Set (Fin r) := {i | i ≤ k ∧ ∀ t ∈ T, t < k → t < i}

def upTo (T : Finset (Fin r)) : Set (Fin r) := {i | ∃ k ∈ T, i ≤ k}

variable (X Y : Matrix (Fin n) (Fin r) E) (T : Finset (Fin r))

def glPart (k : Fin r) : Subgroup (GAd σ J) :=
  levi σ J X Y T ⊓ ptStab σ J (colPerp σ J X (block T k) ⊓ colPerp σ J Y (block T k))

def uPart : Subgroup (GAd σ J) := ptStab σ J (colSpan F X (upTo T) ⊔ colSpan F Y (upTo T))

def part : Option {k // k ∈ T} → Subgroup (GAd σ J)
  | none => uPart σ J X Y T
  | some k => glPart σ J X Y T k.1

end Groups

def sliceSet {G : Type} [Group G] (𝓒 : Set (G → ℂ)) (H L : Subgroup G) (b : G) : Set (H → ℂ) :=
  {f | ∃ φ ∈ 𝓒, ∃ y ∈ L, (∀ t ∈ H, t * y = y * t) ∧ f = fun t : H => φ ((t : G) * y * b)}


open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin in
def cuspOn {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) {m : ℕ}
    (X Y : Matrix (Fin V.rank) (Fin m) D.host.E) (T : Finset (Fin m)) (U : Subgroup (GA D V))
    (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    {W : D.what₂.Tau → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)]
    (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)) (c : D.what₂.Tau → ℕ → ℂ) : Set (GA D V → ℂ) :=
  {φ | φ ∈ formsOn θ V X Y T U ε fr ρ c ∧ ∀ T' : Finset (Fin m), T ⊂ T' → IsConstAlong D.sp.cm.sig V.gram X T' φ 0}

section Slices

theorem exists_finset_sep {X : Type} (A : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ A] :
    ∃ S : Finset X, ∀ f ∈ A, (∀ x ∈ S, f x = 0) → f = 0 := by
  classical
  let ev : X → Module.Dual ℂ A := fun x => (LinearMap.proj x).comp A.subtype
  have hfg : (Submodule.span ℂ (Set.range ev)).FG := IsNoetherian.noetherian _
  obtain ⟨s, hs, e⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  obtain ⟨s', -, rfl⟩ := Finset.subset_set_image_iff.1 (by rwa [Set.image_univ] : (s : Set (Module.Dual ℂ A)) ⊆ ev '' Set.univ)
  refine ⟨s', fun f hf h0 => ?_⟩
  have h1 : ∀ l ∈ Submodule.span ℂ ((s'.image ev : Finset _) : Set (Module.Dual ℂ A)), l ⟨f, hf⟩ = 0 := fun l hl => by
    induction hl using Submodule.span_induction with
    | mem l h =>
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 h
      exact h0 x hx
    | zero => rfl
    | add a b _ _ ha hb => simp [ha, hb]
    | smul a b _ hb => simp [hb]
  funext x
  exact h1 (ev x) (e ▸ Submodule.subset_span ⟨x, rfl⟩)

theorem finiteDimensional_of_slices {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} (A : ∀ i, Submodule ℂ (X i → ℂ))
    [∀ i, FiniteDimensional ℂ (A i)] (𝓕 : Set ((∀ i, X i) → ℂ))
    (h : ∀ f ∈ 𝓕, ∀ i x, (fun t => f (Function.update x i t)) ∈ A i) :
    FiniteDimensional ℂ (Submodule.span ℂ 𝓕) := by
  let P : Submodule ℂ ((∀ i, X i) → ℂ) :=
    { carrier := {f | ∀ i x, (fun t => f (Function.update x i t)) ∈ A i}
      add_mem' := fun {a b} ha hb i x => (A i).add_mem (ha i x) (hb i x)
      zero_mem' := fun i _ => (A i).zero_mem
      smul_mem' := fun a f hf i x => (A i).smul_mem a (hf i x) }
  choose S hS using fun i => exists_finset_sep (A i)
  let ev : P →ₗ[ℂ] ((∀ i, S i) → ℂ) :=
    { toFun := fun f s => f.1 fun i => (s i).1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have key : ∀ f : P, ev f = 0 → ∀ I : Finset ι, ∀ x : ∀ i, X i, (∀ i, i ∉ I → x i ∈ S i) → f.1 x = 0 := by
    intro f hf I
    induction I using Finset.induction_on with
    | empty =>
      intro x hx
      exact congrFun hf fun i => ⟨x i, hx i (by simp)⟩
    | insert a I _ ih =>
      intro x hx
      have := hS a _ (f.2 a x) fun t ht => ih _ fun i hi => by
        by_cases e : i = a
        · subst e; simpa using ht
        · rw [Function.update_of_ne e]
          exact hx i (by simp [e, hi])
      simpa using congrFun this (x a)
  have hinj : Function.Injective ev := (injective_iff_map_eq_zero ev).2 fun f hf =>
    Subtype.ext (funext fun x => key f hf Finset.univ x (by simp))
  haveI : FiniteDimensional ℂ P := FiniteDimensional.of_injective ev hinj
  exact Submodule.finiteDimensional_of_le (S₂ := P) (Submodule.span_le.2 fun f hf i x => h f hf i x)

end Slices

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
end
end
