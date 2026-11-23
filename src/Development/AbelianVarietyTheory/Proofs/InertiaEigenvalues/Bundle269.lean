module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle001
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle184
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle165
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
public import Mathlib.RepresentationTheory.FinGroupCharZero
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.DualLattices.Bundle010

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Cyc

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
open scoped TensorProduct

theorem exists_basis_of_fullLattice {R F M V ι : Type} [CommRing R] [IsDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] [AddCommGroup M] [Module R M] [AddCommGroup V] [Module F V]
    (f : M →+ V) (hf : Function.Injective f)
    (hs : ∀ (c : R) (m : M), f (c • m) = algebraMap R F c • f m)
    (hfull : ∀ v : V, ∃ c : R, c ≠ 0 ∧ ∃ m, algebraMap R F c • v = f m)
    (b0 : Module.Basis ι R M) :
    ∃ b : Module.Basis ι F V, (∀ j, b j = f (b0 j)) ∧
      ∀ m i, b.repr (f m) i = algebraMap R F (b0.repr m i) := by
  letI : Module R V := Module.compHom V (algebraMap R F)
  haveI : IsScalarTower R F V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let g : M →ₗ[R] V := { toFun := f, map_add' := map_add f, map_smul' := hs }
  haveI : IsLocalizedModule (nonZeroDivisors R) g :=
    { map_units := fun s => by
        have h0 : algebraMap R F s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
        rw [Module.End.isUnit_iff]
        exact MulAction.bijective (β := V) (Units.mk0 _ h0 : Fˣ)
      surj := fun v => by
        obtain ⟨c, hc, m, hm⟩ := hfull v
        exact ⟨(m, ⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩), hm⟩
      exists_of_eq := fun h => ⟨1, by rw [hf h]⟩ }
  exact ⟨b0.ofIsLocalizedModule F (nonZeroDivisors R) g,
    fun j => b0.ofIsLocalizedModule_apply F _ g j,
    fun m i => b0.ofIsLocalizedModule_repr_apply F _ g m i⟩

theorem exists_basis_of_locLat {R G F LL O ι : Type} [CommRing R] [IsDomain R] [Group G]
    [TopologicalSpace G] [Field F] [Field LL] [Algebra F LL] [CommRing O] [Algebra O LL]
    [TopologicalSpace LL] [Algebra R F] [IsFractionRing R F] [Algebra R O] [Fintype ι]
    (T : LocLat G F LL O)
    (hc : ∀ c : R, algebraMap O LL (algebraMap R O c) = algebraMap F LL (algebraMap R F c))
    (hden : ∀ a : LL, ∃ c : R, c ≠ 0 ∧
      ∃ o : O, algebraMap O LL o = algebraMap F LL (algebraMap R F c) * a) :
    letI : Module R ↥T.L.T := Module.compHom ↥T.L.T (algebraMap R O)
    ∀ b0 : Module.Basis ι R ↥T.L.T, ∃ b : Module.Basis ι F T.V, (∀ j, b j = (b0 j : T.V)) ∧
      (∀ (m : ↥T.L.T) i, b.repr (m : T.V) i = algebraMap R F (b0.repr m i)) ∧
      (∀ (a : O) j i, b.repr (algebraMap O LL a • b j) i =
        algebraMap R F (b0.repr ⟨_, T.L.T.smul_mem a (b0 j).2⟩ i)) ∧
      ∀ v : T.V, (∀ i, ∃ c : R, b.repr v i = algebraMap R F c) → v ∈ T.L.T := by
  letI : Module R ↥T.L.T := Module.compHom ↥T.L.T (algebraMap R O)
  intro b0
  have key : ∀ (c : R) (w : T.V), algebraMap R F c • w = algebraMap R O c • w := by
    intro c w
    rw [← algebraMap_smul LL (algebraMap R F c) w, ← algebraMap_smul LL (algebraMap R O c) w, hc]
  have hfull : ∀ v : T.V, ∃ c : R, c ≠ 0 ∧ algebraMap R F c • v ∈ T.L.T := by
    intro v
    have hv : v ∈ Submodule.span LL (T.L.T : Set T.V) := by rw [T.L.span]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
    | zero => exact ⟨1, one_ne_zero, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, hx⟩ := hx
      obtain ⟨c', hc', hy⟩ := hy
      refine ⟨c * c', mul_ne_zero hc hc', ?_⟩
      rw [smul_add]
      refine add_mem ?_ ?_
      · rw [mul_comm, map_mul, mul_smul, key c']
        exact T.L.T.smul_mem _ hx
      · rw [map_mul, mul_smul, key c]
        exact T.L.T.smul_mem _ hy
    | smul a x _ hx =>
      obtain ⟨c, hc, hx⟩ := hx
      obtain ⟨c', hc', o, ho⟩ := hden a
      refine ⟨c' * c, mul_ne_zero hc' hc, ?_⟩
      have := T.L.T.smul_mem o hx
      rw [← algebraMap_smul LL, ho, mul_smul, algebraMap_smul,
        smul_comm a (algebraMap R F c) x] at this
      rwa [map_mul, mul_smul]
  obtain ⟨b, hb, hr⟩ := exists_basis_of_fullLattice (R := R) (F := F)
    (T.L.T.subtype.toAddMonoidHom) Subtype.val_injective
    (fun c m => (key c m).symm)
    (fun v => by
      obtain ⟨c, hc, hv⟩ := hfull v
      exact ⟨c, hc, ⟨_, hv⟩, rfl⟩) b0
  refine ⟨b, hb, hr, fun a j i => ?_, fun v hv => ?_⟩
  · rw [← hr, hb, algebraMap_smul]
    rfl
  · rw [← b.sum_repr v]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c, hc⟩ := hv i
    rw [hc, key, hb]
    exact T.L.T.smul_mem _ (b0 i).2

theorem exists_ratBasis_of_isMat : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∃ b : Module.Basis (Fin d) ℚ_[l] T.V, (∀ (g : ↥(GK K)) (i j : Fin d), M (g : GQ l) i j = algebraMap ℚ_[l] (PadicComplex l) (b.repr (T.ρ g (b j)) i)) ∧ (∀ (a : ↥(OL LL)) (i j : Fin d), A a i j = algebraMap ℚ_[l] (PadicComplex l) (b.repr ((a : ↥LL.1) • b j) i)) ∧ ∀ v : T.V, v ∈ T.L.T ↔ ∀ i, ‖b.repr v i‖ ≤ 1 := by
  intro l _ K LL T d M A h
  letI := zlMod LL T
  obtain ⟨b0, hM, hA⟩ := h
  obtain ⟨b, hb, hr, ha, hv⟩ := exists_basis_of_locLat (R := ℤ_[l]) T (fun _ => rfl) (fun a => by
    have ha : IsAlgebraic ℤ_[l] a :=
      (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).2 (Algebra.IsAlgebraic.isAlgebraic a)
    obtain ⟨c, hc, hint⟩ := ha.exists_integral_multiple
    exact ⟨c, hc, ⟨c • a, hint⟩, Algebra.smul_def c a⟩) b0
  refine ⟨b, fun g i j => ?_, fun a i j => ?_, fun v => ⟨fun h i => ?_, fun h => ?_⟩⟩
  · have e : T.ρ g (b j) = ((actTZ LL T g (b0 j) : ↥T.L.T) : T.V) := congrArg (T.ρ g) (hb j)
    rw [e]
    exact (hM g i j).trans
      (congrArg (algebraMap ℚ_[l] (PadicComplex l)) (hr (actTZ LL T g (b0 j)) i).symm)
  · exact (hA a i j).trans (congrArg (algebraMap ℚ_[l] (PadicComplex l)) (ha a j i).symm)
  · exact (congrArg norm (hr ⟨v, h⟩ i)).trans_le (b0.repr ⟨v, h⟩ i).2
  · exact hv v fun i => ⟨⟨_, h i⟩, rfl⟩

end GlobalTheory.Cyc
end
end

section

section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.FieldAut

section Rep

variable {G : Type} [Group G]

def galRep (σ : ℂ ≃+* ℂ) (V : FDRep ℂ G) : Representation ℂ G (Fin (Module.finrank ℂ V) → ℂ) :=
  ((Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin (Module.finrank ℂ V))).toMulEquiv.toMonoidHom).comp
    (((σ : ℂ →+* ℂ).mapMatrix (m := Fin (Module.finrank ℂ V))).toMonoidHom.comp
      (((LinearMap.toMatrixAlgEquiv (Module.finBasis ℂ V)).toMulEquiv.toMonoidHom).comp V.ρ))

theorem trace_galRep (σ : ℂ ≃+* ℂ) (V : FDRep ℂ G) (x : G) :
    LinearMap.trace ℂ _ (galRep σ V x) = σ (V.character x) := by
  have h1 : galRep σ V x =
      Matrix.toLin' ((LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) (V.ρ x)).map σ) := rfl
  have h2 : V.character x =
      (LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) (V.ρ x)).trace :=
    LinearMap.trace_eq_matrix_trace ℂ (Module.finBasis ℂ V) (V.ρ x)
  rw [h1, Matrix.trace_toLin'_eq, h2]
  simp [Matrix.trace]

variable [Fintype G]

theorem isIrr_comp (σ : ℂ ≃+* ℂ) {χ : G → ℂ} (h : IsIrr χ) : IsIrr (σ ∘ χ) := by
  obtain ⟨V, hs, hV⟩ := h
  have hW : ∀ x, (FDRep.of (galRep σ V)).character x = σ (V.character x) := fun x => trace_galRep σ V x
  refine ⟨FDRep.of (galRep σ V), ?_, fun x => by rw [hW, hV]; rfl⟩
  rw [FDRep.simple_iff_char_is_norm_one]
  have h := congrArg σ ((FDRep.simple_iff_char_is_norm_one V).1 hs)

  rw [map_natCast, map_sum] at h
  rw [← h]
  exact Finset.sum_congr rfl fun x _ => by rw [map_mul, hW, hW]

theorem coeff_zOf (χ : G → ℂ) (y : G) :
    (zOf χ).coeff y = χ 1 / (Fintype.card G : ℂ) * χ y⁻¹ := by
  simp only [zOf, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem mapRange_zOf (σ : ℂ ≃+* ℂ) (χ : G → ℂ) :
    (zOf χ).coeff.mapRange σ (map_zero σ) = (zOf (σ ∘ χ)).coeff := by
  ext y
  rw [Finsupp.mapRange_apply, coeff_zOf, coeff_zOf]
  simp only [Function.comp, map_mul, map_div₀, map_natCast]

theorem ip_comp (σ : ℂ ≃+* ℂ) (α β : G → ℂ) : ip (σ ∘ α) (σ ∘ β) = σ (ip α β) := by

  simp only [ip, Function.comp, map_mul, map_sum, map_inv₀, map_natCast]

end Rep

variable {g : ℕ} [Fact g.Prime]

theorem hc_comp (σ : ℂ ≃+* ℂ) (a b : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ) (n : ℕ) :
    hc a b (σ ∘ α) (σ ∘ β) n = σ ∘ hc a b α β n := by
  funext x

  simp only [hc, hcT, Function.comp, map_mul, map_sum, map_inv₀, map_natCast, apply_ite σ, map_zero]

theorem degL_map (σ : ℂ ≃+* ℂ) (L : List (Pc g)) :
    degL (L.map fun p => (⟨p.1, σ ∘ p.2⟩ : Pc g)) = degL L := by
  simp [degL, List.map_map, Function.comp_def]

theorem hcL_map (σ : ℂ ≃+* ℂ) (L : List (Pc g)) :
    ∀ n, hcL (L.map fun p => (⟨p.1, σ ∘ p.2⟩ : Pc g)) n = σ ∘ hcL L n := by
  induction L with
  | nil =>
    intro n
    funext x
    simp [hcL_nil]
  | cons p L ih =>
    intro n
    show hc p.1 (degL (L.map fun p => (⟨p.1, σ ∘ p.2⟩ : Pc g))) (σ ∘ p.2)
      (hcL (L.map fun p => (⟨p.1, σ ∘ p.2⟩ : Pc g)) (degL (L.map fun p => (⟨p.1, σ ∘ p.2⟩ : Pc g)))) n = _
    rw [degL_map, ih, hc_comp, hcL_cons]

theorem res_comp (σ : ℂ ≃+* ℂ) (a b : ℕ) {n : ℕ} (χ : Gn g n → ℂ) (h₁ : Gn g a) (h₂ : Gn g b) :
    res a b (σ ∘ χ) h₁ h₂ = σ (res a b χ h₁ h₂) := by

  simp only [res, Function.comp, map_mul, map_sum, map_inv₀, map_pow, map_natCast, apply_ite σ, map_zero]

theorem isCusp_comp (σ : ℂ ≃+* ℂ) {d : ℕ} {χ : Gn g d → ℂ} (h : IsCusp χ) : IsCusp (σ ∘ χ) :=
  ⟨h.1, isIrr_comp σ h.2.1, fun a ha ha' => by rw [res_comp, h.2.2 a ha ha', map_zero]⟩

end GlobalTheory.CompanionTheory.FieldAut

theorem GlobalTheory.CompanionTheory.FieldAut.action : ∀ (g : ℕ) [Fact g.Prime] (σ : ℂ ≃+* ℂ), (∀ (G : Type) [Group G] [Fintype G] (χ : G → ℂ), (IsIrr χ → IsIrr (σ ∘ χ)) ∧ (zOf χ).coeff.mapRange σ (map_zero σ) = (zOf (σ ∘ χ)).coeff ∧ ∀ β, ip (σ ∘ χ) (σ ∘ β) = σ (ip χ β)) ∧ (∀ (L : List (Pc g)) (n : ℕ), hcL (L.map fun p => (⟨p.1, σ ∘ p.2⟩ : Pc g)) n = σ ∘ hcL L n) ∧ ∀ (d : ℕ) (χ : Gn g d → ℂ), IsCusp χ → IsCusp (σ ∘ χ) := by
  intro g _ σ
  exact ⟨fun G _ _ χ => ⟨GlobalTheory.CompanionTheory.FieldAut.isIrr_comp σ, GlobalTheory.CompanionTheory.FieldAut.mapRange_zOf σ χ,
    GlobalTheory.CompanionTheory.FieldAut.ip_comp σ χ⟩, fun L n => GlobalTheory.CompanionTheory.FieldAut.hcL_map σ L n,
    fun d χ h => GlobalTheory.CompanionTheory.FieldAut.isCusp_comp σ h⟩

end
end

section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
theorem _root_.GlobalTheory.Adopt.complexFieldAut_acts_harishChandra_characters : ∀ (g : ℕ) [Fact g.Prime] (σ : ℂ ≃+* ℂ), (∀ (G : Type) [Group G] [Fintype G] (χ : G → ℂ), (IsIrr χ → IsIrr (σ ∘ χ)) ∧ (zOf χ).coeff.mapRange σ (map_zero σ) = (zOf (σ ∘ χ)).coeff ∧ ∀ β, ip (σ ∘ χ) (σ ∘ β) = σ (ip χ β)) ∧ (∀ (L : List (Pc g)) (n : ℕ), hcL (L.map fun p => (⟨p.1, σ ∘ p.2⟩ : Pc g)) n = σ ∘ hcL L n) ∧ ∀ (d : ℕ) (χ : Gn g d → ℂ), IsCusp χ → IsCusp (σ ∘ χ) := by
  first | exact @GlobalTheory.CompanionTheory.FieldAut.action | exact GlobalTheory.CompanionTheory.FieldAut.action | (intros; apply GlobalTheory.CompanionTheory.FieldAut.action <;> assumption)

end
end

section

noncomputable section

namespace GlobalTheory.Cyc

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem actC_eq_σC (g : GQ l) (y : PadicComplex l) : AI.actC g y = Formalism.Per.σC g y := by
  have hc : Continuous (AI.actC g) :=
    (AddMonoidHomClass.isometry_of_norm (AI.actC g) (AI.actC_norm g)).continuous
  induction y using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq hc (by apply GlobalTheory.RingIface.sigC_cont)
  | ih a => exact (AI.actC_ext g a).trans (GlobalTheory.RingBasics.σC_coe g a).symm

theorem actT_eq_σF (g : GQ l) (x : OCb l) : AI.actT g x = Formalism.Per.σF g x := by
  refine Perfection.ext fun n => ?_
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff n x)
  obtain ⟨y', h1, h2⟩ := AI.actT_coeff g x n y hy.symm
  have h3 : y' = Formalism.Per.σO g y := Subtype.ext ((h1.trans (actC_eq_σC AI g y)).trans
    (by symm; apply GlobalTheory.RingIface.sigO_coe))
  refine h2.trans ?_
  rw [h3]
  exact (GlobalTheory.AdicMaps.coeff_galois l g x n y hy.symm).symm

theorem ζ_add_pow (j n : ℕ) : AI.ζ (j + n) ^ l ^ n = AI.ζ j := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, ← add_assoc, AI.ζ_succ, ih]

theorem coeff_εroot (j n : ℕ) : PreTilt.coeff n (AI.εroot j) =
    Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (AI.ζ (j + n)) := by
  rw [← AI.ε_coeff, LocAinf.εroot, PreTilt.coeff_iterate_frobeniusEquiv_symm, add_comm]

theorem untilt_εroot (j : ℕ) : (AI.εroot j).untilt = AI.ζ j := by
  refine Perfection.teichmuller_spec (I := Ideal.span {((l : ℕ) : OC l)}) fun n => ?_
  refine ⟨AI.ζ (j + n), (coeff_εroot AI j n).symm, ?_⟩
  rw [ζ_add_pow]

theorem isTheta_fontaineTheta : IsTheta AI (WittVector.fontaineTheta (OC l) l) := by
  have hprim : IsPrimitiveRoot (((frobeniusEquiv (OCb l) l).symm AI.ε).untilt) l := by
    have h : ((frobeniusEquiv (OCb l) l).symm AI.ε).untilt = AI.ζ 1 := untilt_εroot AI 1
    rw [h]
    have h1 : AI.ζ 1 ^ l = 1 := (AI.ζ_succ 0).trans AI.ζ_zero
    have h2 := IsPrimitiveRoot.orderOf (AI.ζ 1)
    rwa [orderOf_eq_prime h1 AI.ζ_one] at h2
  refine ⟨fun x y h => ?_, ?_, fun g a => ?_, fun a => ?_, fun j => ?_⟩
  · rw [← Ideal.Quotient.eq, WittVector.fontaineTheta_teichmuller, ← h]
    exact PreTilt.mk_untilt_eq_coeff_zero x
  · exact ReciprocityTheory.PGsh.Ainf.theta_surj l (OC l) (PadicComplexInt.integers l)
  · have e : AI.actW g a = Formalism.Per.σA g a := WittVector.ext fun n =>
      (actT_eq_σF AI g (a.coeff n)).trans (by symm; apply GlobalTheory.RingIface.sigA_coeff)
    rw [e, actC_eq_σC]
    exact (congrArg Subtype.val (GlobalTheory.RingBasics.θ_σA g a)).trans (by apply GlobalTheory.RingIface.sigO_coe)
  · rw [← RingHom.mem_ker,
      ReciprocityTheory.PGsh.Ainf.ker_theta l (OC l) (PadicComplexInt.integers l) AI.ε hprim,
      Ideal.mem_span_singleton]
    rfl
  · rw [WittVector.fontaineTheta_teichmuller, untilt_εroot]

theorem exists_isTheta : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    ∃ θ : Ainf l →+* OC l, IsTheta AI θ :=
  fun _ _ _ AI => ⟨_, isTheta_fontaineTheta AI⟩

end GlobalTheory.Cyc
end
end

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

noncomputable section

namespace GlobalTheory.GLq.ZOrth

open GlobalTheory.BadShare GlobalTheory.BadShare.Basic

theorem zOf_eq_alg {G : Type} [Group G] [Fintype G] (χ : G → ℂ) : zOf χ = alg (zc χ) := rfl

theorem ip_simple {G : Type} [Group G] [Fintype G] (V W : FDRep ℂ G) [CategoryTheory.Simple V]
    [CategoryTheory.Simple W] :
    ip V.character W.character = if V.character = W.character then 1 else 0 := by
  haveI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_ne_zero)
  have h := FDRep.char_orthonormal V W
  rw [Nat.card_eq_fintype_card] at h
  unfold ip
  rw [h]
  by_cases hi : Nonempty (V ≅ W)
  · rw [if_pos hi, if_pos (FDRep.char_iso hi.some)]
  · rw [if_neg hi]
    by_cases hc : V.character = W.character
    · exfalso
      have h1 := FDRep.char_orthonormal V V
      rw [if_pos ⟨CategoryTheory.Iso.refl V⟩] at h1
      have h2 := FDRep.char_orthonormal V W
      rw [if_neg hi, ← hc] at h2
      rw [h1] at h2
      simp at h2
    · rw [if_neg hc]

theorem zorth : ∀ (G : Type) [Group G] [Fintype G] (χ χ' : G → ℂ), IsIrr χ → IsIrr χ' → (zOf χ * zOf χ' = if χ = χ' then zOf χ else 0) ∧ (∀ a, zOf χ * a = a * zOf χ) ∧ ip χ χ' = if χ = χ' then 1 else 0 := by
  intro G _ _ χ χ' hχ hχ'
  obtain ⟨V, hV, hVχ⟩ := hχ
  obtain ⟨W, hW, hWχ⟩ := hχ'
  have eV : V.character = χ := funext hVχ
  have eW : W.character = χ' := funext hWχ
  subst eV eW
  obtain ⟨⟨hidem, _⟩, hcen, horth, _⟩ := GlobalTheory.BadShare.ZCalc.zc_calc G V
  refine ⟨?_, ?_, ip_simple V W⟩
  · rw [zOf_eq_alg, zOf_eq_alg, ← alg_conv]
    by_cases hc : V.character = W.character
    · rw [if_pos hc, ← hc, hidem]
    · rw [if_neg hc, horth W hc]
      unfold alg; simp
  · intro a
    rw [zOf_eq_alg, ← alg_coeff a, ← alg_conv, ← alg_conv, hcen]
end GlobalTheory.GLq.ZOrth
end
end

section

noncomputable section

namespace GlobalTheory.Cyc.Decomp

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

theorem act_eq_of_mem_intC {l : ℕ} [Fact l.Prime]
    {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    {F : IntermediateField ℚ_[l] (Om l)} {σ : GQ l} (hσ : σ ∈ F.fixingSubgroup)
    {y : PadicComplex l} (hy : y ∈ intC F) : act σ y = y := by
  simp only [intC, inC, Set.mem_ofPred_eq, Set.mem_image, SetLike.mem_coe] at hy
  obtain ⟨⟨x, hxF, rfl⟩, -⟩ := hy
  rw [ha.1 σ x, (IntermediateField.mem_fixingSubgroup_iff F σ).1 hσ x hxF]

theorem isDec_of_matrix : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ) (K : FinExt l) (m d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (D : Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l), IsActC act → IsGen χ K m g → (∀ i j, ContinuousOn (fun σ => M σ i j) (Gj K m)) → (∀ σ ∈ Gj K m, ∀ τ ∈ Gj K m, M (σ * τ) = M σ * M τ) → (∀ σ ∈ Gj K m, ∀ τ ∈ Gj K m, (M τ).map (act σ) = M τ) → (∀ i j, ‖D i j‖ ≤ 1) → (∃ X : Matrix (Fin d) (Fin d) (PadicComplex l), (∀ i j, ‖X i j‖ ≤ 1) ∧ D * X = (l : PadicComplex l) • (1 : Matrix (Fin d) (Fin d) (PadicComplex l))) → (∀ σ ∈ Gj K m, ∃ X : Matrix (Fin d) (Fin d) (PadicComplex l), (∀ i j, X i j ∈ intC (Ks K m)) ∧ M σ * D.map (act σ) = D * X) → (∀ σ ∈ Hinf K, M σ * D.map (act σ) = D) → (∃ X : Matrix (Fin d) (Fin d) (PadicComplex l), (∀ i j, ‖X i j‖ < rho1 l) ∧ M g * D.map (act g) - D = D * X) → ∃ U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l), IsDec act χ K m M D U g := by
  intro l _ act χ K m d M D g ha hg hMc hMmul hMfix hD hDinv hInt hH hgclose
  obtain ⟨Y, hY, hDY⟩ := hDinv
  have hl : (l : PadicComplex l) ≠ 0 := by
    exact_mod_cast (Fact.out : l.Prime).ne_zero

  have hright : D * ((l : PadicComplex l)⁻¹ • Y) = 1 := by
    rw [Matrix.mul_smul, hDY, smul_smul, inv_mul_cancel₀ hl, one_smul]
  have hdet : IsUnit D.det := Matrix.isUnit_det_of_right_inverse hright
  have hinv : D⁻¹ = (l : PadicComplex l)⁻¹ • Y := Matrix.inv_eq_right_inv hright
  have hDD : D⁻¹ * D = 1 := Matrix.nonsing_inv_mul D hdet
  have hDD' : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv D hdet

  have hmapmul : ∀ (e : PadicComplex l ≃+* PadicComplex l) (A B : Matrix (Fin d) (Fin d) (PadicComplex l)),
      (A * B).map e = A.map e * B.map e := by
    intro e A B
    ext i j

    simp [Matrix.mul_apply, map_sum, map_mul]
  have hmapcomp : ∀ σ τ : GQ l, D.map (act (σ * τ)) = (D.map (act τ)).map (act σ) := by
    intro σ τ
    ext i j
    simp only [Matrix.map_apply, map_mul]
    rfl

  refine ⟨fun σ => D⁻¹ * (M σ * D.map (act σ)), hdet, hD, ?_, ⟨hg, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro a b
    rw [hinv, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hl, one_mul]
    exact hY a b
  · intro a b
    simp only [Matrix.mul_apply, Matrix.map_apply]
    refine continuousOn_finsetSum _ fun k _ => continuousOn_const.mul ?_
    refine continuousOn_finsetSum _ fun j _ => (hMc k j).mul ?_
    exact (IsActC.continuous_orbit l act ha (D j b)).continuousOn
  · intro σ hσ a b
    obtain ⟨X, hX, hMX⟩ := hInt σ hσ
    show (D⁻¹ * (M σ * D.map (act σ))) a b ∈ intC (Ks K m)
    rw [hMX, ← Matrix.mul_assoc, hDD, Matrix.one_mul]
    exact hX a b
  · intro σ hσ τ hτ
    obtain ⟨X, hX, hMX⟩ := hInt τ hτ
    have hUτ : D⁻¹ * (M τ * D.map (act τ)) = X := by
      rw [hMX, ← Matrix.mul_assoc, hDD, Matrix.one_mul]

    have hXfix : X.map (act σ) = X := by
      ext i j
      exact act_eq_of_mem_intC ha (show σ ∈ (Ks K m).fixingSubgroup from hσ) (hX i j)
    show D⁻¹ * (M (σ * τ) * D.map (act (σ * τ)))
      = D⁻¹ * (M σ * D.map (act σ)) * (D⁻¹ * (M τ * D.map (act τ)))
    calc D⁻¹ * (M (σ * τ) * D.map (act (σ * τ)))
        = D⁻¹ * (M σ * (M τ * D.map (act τ)).map (act σ)) := by
          rw [hMmul σ hσ τ hτ, hmapmul, hMfix σ hσ τ hτ, hmapcomp]
          simp only [Matrix.mul_assoc]
      _ = D⁻¹ * (M σ * (D.map (act σ) * X)) := by rw [hMX, hmapmul, hXfix]
      _ = D⁻¹ * (M σ * D.map (act σ)) * (D⁻¹ * (M τ * D.map (act τ))) := by
          rw [hUτ]
          simp only [Matrix.mul_assoc]
  · intro σ hσ
    show D⁻¹ * (M σ * D.map (act σ)) = 1
    rw [hH σ hσ, hDD]
  · intro a b
    obtain ⟨X, hX, hMX⟩ := hgclose
    have hU : D⁻¹ * (M g * D.map (act g)) - 1 = X := by
      rw [← hDD, ← Matrix.mul_sub, hMX, ← Matrix.mul_assoc, hDD, Matrix.one_mul]
    show ‖(D⁻¹ * (M g * D.map (act g)) - 1) a b‖ < rho1 l
    rw [hU]
    exact hX a b
  · intro σ hσ
    show D * (D⁻¹ * (M σ * D.map (act σ))) = M σ * D.map (act σ)
    rw [← Matrix.mul_assoc, hDD', Matrix.one_mul]

end GlobalTheory.Cyc.Decomp
end
end
