module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle059
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle052
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle025
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001

@[expose] public section

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.exists_rational_invariant_tensor' : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → SS Γ → ∃ (m : ℕ) (d : Fin m → ℕ) (t : TIdx ι d → ℚ), (∀ g ∈ Γ, act d (fun k => ((t k : ℚ) : ℂ)) g = (fun k => ((t k : ℚ) : ℂ))) ∧ ∀ f, IsInv Γ f → ∃ P : MvPolynomial (TIdx ι d) ℂ, ∀ y : Matrix ι ι ℂ, evC f y = MvPolynomial.eval (act d (fun k => ((t k : ℚ) : ℂ)) y) P := by
  first | exact @GlobalTheory.ClassFin.RatInvTensor.exists_rational_invariant_tensor | exact GlobalTheory.ClassFin.RatInvTensor.exists_rational_invariant_tensor | (intros; apply GlobalTheory.ClassFin.RatInvTensor.exists_rational_invariant_tensor <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem _root_.GlobalTheory.T.sUnits_sup_unitsLocalNormsSqrt_ne_top : ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), admitted F S → δ ∈ sUnits F S → ¬ IsSquare (δ : F) → sUnits F S ⊔ locNorm F δ S ≠ ⊤ := by
  first | exact @GlobalTheory.QNorm.sUnits_sup_locNorm_ne_top | exact GlobalTheory.QNorm.sUnits_sup_locNorm_ne_top | (intros; apply GlobalTheory.QNorm.sUnits_sup_locNorm_ne_top <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep

theorem exists_nat_smul_mem_of_span {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (y : Fin n → E) : ∃ d : ℕ, 0 < d ∧ (d : E) • y ∈ L := by
  first
  | exact @_root_.GlobalTheory.NatMulIntegral.exists_nat_smul_mem
  | exact _root_.GlobalTheory.NatMulIntegral.exists_nat_smul_mem
  | (apply _root_.GlobalTheory.NatMulIntegral.exists_nat_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMulIntegral.exists_nat_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMulIntegral.exists_nat_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMulIntegral.exists_nat_smul_mem ..)

theorem exists_nat_smul_map_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (φ : (Fin n → E) →ₗ[E] (Fin n → E)) : ∃ d : ℕ, 0 < d ∧ ∀ v ∈ L, (d : E) • φ v ∈ L := by
  classical
  choose d hd hdL using exists_nat_smul_mem_of_span L hL
  obtain ⟨S, hS⟩ := hfg
  refine ⟨∏ s ∈ S, d (φ s), Finset.prod_pos fun s _ => hd _, ?_⟩
  intro v hv
  rw [← hS] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.prod_erase_mul S _ (Finset.mem_coe.1 hx), Nat.cast_mul, mul_smul,
      Nat.cast_smul_eq_nsmul E (∏ s ∈ S.erase x, d (φ s))]
    exact L.toAddSubmonoid.nsmul_mem (hdL _) _
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _), smul_add]
    exact L.add_mem hx hy
  | smul a x _ hx =>
    have h1 : φ (a • x) = (a : E) • φ x := φ.map_smul (a : E) x
    rw [h1, smul_comm]
    exact L.smul_mem a hx

theorem exists_refl_correction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (x : Fin n → E) (u : E) (N D : ℕ), hermE c G x x ≠ 0 → u * c u = 1 → 0 < N → 0 < D → ∃ u' : E, u' * c u' = 1 ∧ CongAt L N D (refl c G x (u' / u)) ∧ ∃ s : 𝓞 E, SplitOr c N s ∧ ∀ v ∈ L, s • (refl c G x u' *ᵥ v) ∈ L ∧ s • (refl c G x u'⁻¹ *ᵥ v) ∈ L := by
  intro F E _ _ _ _ _ c n G hG L hfg hL x u N D hx hu hN hD
  have hap := (GlobalTheory.UnRep.ReflLaws.refl_laws F E c n G hG x hx).1
  let φ : (Fin n → E) →ₗ[E] (Fin n → E) :=
    { toFun := fun v => (hermE c G v x / hermE c G x x) • x
      map_add' := by
        intro v w
        rw [← add_smul, ← add_div]
        congr 2
        simp [hermE, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro a v
        rw [RingHom.id_apply, smul_smul, ← mul_div_assoc]
        congr 2
        simp [hermE, Finset.mul_sum, mul_assoc] }
  obtain ⟨d, hd, hdL⟩ := exists_nat_smul_map_mem L hfg hL φ
  have hap' : ∀ a v, refl c G x a *ᵥ v = v + (a - 1) • φ v := by
    intro a v
    rw [hap]
    show _ = v + (a - 1) • ((hermE c G v x / hermE c G x x) • x)
    rw [smul_smul, mul_div_assoc]
  obtain ⟨u', hu', ⟨t, ht, b, hb⟩, s, hs, ⟨b₁, hb₁⟩, b₂, hb₂⟩ :=
    GlobalTheory.T.normOne_approximation_at_level_primes F E c hG.1 hG.2.1 u N (D * d) hu hN (Nat.mul_pos hD hd)
  have key : ∀ (a : E) (b : 𝓞 E), (s : E) * (a - 1) = ((D * d : ℕ) : E) * (b : E) →
      ∀ v ∈ L, s • (refl c G x a *ᵥ v) ∈ L := by
    intro a b hb v hv
    rw [hap', smul_add]
    refine L.add_mem (L.smul_mem s hv) ?_
    have : s • ((a - 1) • φ v) = ((D : 𝓞 E) * b) • ((d : E) • φ v) := by
      show (s : E) • ((a - 1) • φ v) = (((D : 𝓞 E) * b : 𝓞 E) : E) • ((d : E) • φ v)
      rw [smul_smul, smul_smul, hb]
      congr 1
      push_cast
      ring
    rw [this]
    exact L.smul_mem _ (hdL v hv)
  refine ⟨u', hu', ⟨t, ht, fun v hv => ⟨b • ((d : E) • φ v), L.smul_mem b (hdL v hv), ?_⟩⟩,
    s, hs, fun v hv => ⟨key _ _ hb₁ v hv, key _ _ hb₂ v hv⟩⟩
  rw [hap', add_sub_cancel_left, ← Nat.cast_smul_eq_nsmul E t, ← Nat.cast_smul_eq_nsmul E D]
  show _ = (D : E) • ((b : E) • ((d : E) • φ v))
  rw [smul_smul, smul_smul, smul_smul, hb]
  congr 1
  push_cast
  ring

end GlobalTheory.UnRep
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.pow_of_sUnit_localPower_at_places : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [DecidableEq (HeightOneSpectrum (𝓞 F))] (ζ : F) (S T : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → AdmP p F S → sUnits F (S ∪ T) ⊔ finPow p F T = ⊤ → ∀ y ∈ sUnits F (S ∪ T), y ∈ finPow p F S → ∃ r : F, r ^ p = (y : F) := by
  first | exact @GlobalTheory.CNorm.pow_of_mem_sUnits_union_of_mem_finPow | exact GlobalTheory.CNorm.pow_of_mem_sUnits_union_of_mem_finPow | (intros; apply GlobalTheory.CNorm.pow_of_mem_sUnits_union_of_mem_finPow <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.IdeleParts

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isOpen_nsmul_adelicCompletion_integers (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (N : ℕ) (hN : 0 < N) :
    letI : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) :=
      moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)
    IsOpen {z : GlobalTheory.AdLat.RA F E | ∃ y ∈ GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)), z = N • y} := by
  letI : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) :=
      moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)
  let L : Submodule (𝓞 E) (Fin 1 → E) :=
    (1 : Submodule (𝓞 E) E).comap (LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin 1 => E) 0)
  have hL : ∀ x : Fin 1 → E, x ∈ L ↔ x 0 ∈ Set.range (algebraMap (𝓞 E) E) := by
    intro x
    simp only [L, Submodule.mem_comap, Submodule.mem_one, LinearMap.proj_apply, Set.mem_range]
  have hspan : Submodule.span E (L : Set (Fin 1 → E)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have h1 : (fun _ => (1 : E)) ∈ L := (hL _).2 ⟨1, map_one _⟩
    have : x = x 0 • (fun _ : Fin 1 => (1 : E)) := by
      funext i
      rw [Subsingleton.elim i 0]
      simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
  have ho := (GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat F E 1 L hspan).1 N hN
  have hc : Continuous (fun z : GlobalTheory.AdLat.RA F E => fun _ : Fin 1 => z) := continuous_pi fun _ => continuous_id
  have h1 : ∀ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin 1 → E)),
      y 0 ∈ GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)) := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      exact AddSubgroup.subset_closure ⟨a, ha, x 0, (hL x).1 hx, rfl⟩
    | zero => exact zero_mem _
    | add u v _ _ hu hv => exact add_mem hu hv
    | neg u _ hu => exact neg_mem hu
  have h2 : ∀ y ∈ GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)),
      (fun _ : Fin 1 => y) ∈ GlobalTheory.AdLat.hat F (L : Set (Fin 1 → E)) := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      exact AddSubgroup.subset_closure ⟨a, ha, fun _ => x, (hL _).2 hx, rfl⟩
    | zero => exact zero_mem _
    | add u v _ _ hu hv => exact add_mem hu hv
    | neg u _ hu => exact neg_mem hu
  convert ho.preimage hc using 1
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, h2 y hy, rfl⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨y 0, h1 y hy, congrFun h 0⟩

theorem integralFiniteAdeles_eq_adelicCompletion_integers (D : D7) :
    intAE D = GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)) := by
  unfold intAE GlobalTheory.AdLat.hat1
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, x, rfl⟩
    exact ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
    exact ⟨a, ha, x, rfl⟩

theorem exists_units_parts {R A B : Type} [Ring R] [Ring A] [Ring B] [TopologicalSpace R] [TopologicalSpace A]
    [TopologicalSpace B] (e : R ≃+* A × B) (hec : Continuous e) (hes : Continuous e.symm)
    (f : R → A) (g : R → B) (he : ∀ z, (e z).1 = f z ∧ (e z).2 = g z) :
    ∃ a b : Rˣ →* Rˣ, Continuous a ∧ Continuous b ∧ (∀ x, x = a x * b x) ∧
      (∀ x, f (a x : R) = f (x : R) ∧ g (a x : R) = 1) ∧ ∀ x, f (b x : R) = 1 ∧ g (b x : R) = g (x : R) := by
  let a0 : R →* R := e.symm.toRingHom.toMonoidHom.comp
    ((MonoidHom.inl _ _).comp ((MonoidHom.fst _ _).comp e.toRingHom.toMonoidHom))
  let b0 : R →* R := e.symm.toRingHom.toMonoidHom.comp
    ((MonoidHom.inr _ _).comp ((MonoidHom.snd _ _).comp e.toRingHom.toMonoidHom))
  have ha0 : ∀ z, a0 z = e.symm ((e z).1, 1) := fun z => rfl
  have hb0 : ∀ z, b0 z = e.symm (1, (e z).2) := fun z => rfl
  have hac : Continuous a0 := by
    rw [show (a0 : R → R) = fun z => e.symm ((e z).1, 1) from funext ha0]
    exact hes.comp ((continuous_fst.comp hec).prodMk continuous_const)
  have hbc : Continuous b0 := by
    rw [show (b0 : R → R) = fun z => e.symm (1, (e z).2) from funext hb0]
    exact hes.comp (continuous_const.prodMk (continuous_snd.comp hec))
  refine ⟨Units.map a0, Units.map b0, Continuous.units_map a0 hac, Continuous.units_map b0 hbc,
    fun x => ?_, fun x => ?_, fun x => ?_⟩
  · apply Units.ext
    rw [Units.val_mul, Units.coe_map, Units.coe_map, ha0, hb0, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
    exact (e.symm_apply_apply _).symm
  · rw [Units.coe_map, ha0, ← (he _).1, ← (he _).2, e.apply_symm_apply]
    exact ⟨(he _).1, rfl⟩
  · rw [Units.coe_map, hb0, ← (he _).1, ← (he _).2, e.apply_symm_apply]
    exact ⟨rfl, (he _).2⟩

theorem congr_open_and_parts : ∀ (D : D7), (∀ N : ℕ, 0 < N → IsOpen {x : (AE D)ˣ | finPart D (x : AE D) ∈ intAE D ∧ finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D ∧ ∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y}) ∧ ∃ a b : (AE D)ˣ →* (AE D)ˣ, Continuous a ∧ Continuous b ∧ (∀ x, x = a x * b x) ∧ (∀ x, infPart D (a x : AE D) = infPart D (x : AE D) ∧ finPart D (a x : AE D) = 1) ∧ ∀ x, infPart D (b x : AE D) = 1 ∧ finPart D (b x : AE D) = finPart D (x : AE D) := by
  intro D
  letI tf : TopologicalSpace (Af D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E)
  letI ti : TopologicalSpace (Ainf D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Ainf D.host.F) (Ainf D.host.F ⊗[D.host.F] D.host.E)
  obtain ⟨e, he, hec, hes⟩ : ∃ e : AE D ≃+* (Ainf D.host.F ⊗[D.host.F] D.host.E) × (Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ z, (e z).1 = infPart D z ∧ (e z).2 = finPart D z) ∧ Continuous e ∧ Continuous e.symm :=
    GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hfc : Continuous (finPart D) := by
    have : (finPart D : AE D → _) = fun z => (e z).2 := funext fun z => (he z).2.symm
    rw [this]
    exact continuous_snd.comp hec
  refine ⟨fun N hN => ?_, ?_⟩
  · haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
    haveI : ContinuousAdd (Af D.host.F ⊗[D.host.F] D.host.E) :=
      IsModuleTopology.toContinuousAdd (Af D.host.F) _
    have hN' : IsOpen {z : Af D.host.F ⊗[D.host.F] D.host.E | ∃ y ∈ intAE D, z = N • y} := by
      rw [integralFiniteAdeles_eq_adelicCompletion_integers]
      exact isOpen_nsmul_adelicCompletion_integers D.host.F D.host.E N hN
    have h1 : IsOpen {z : Af D.host.F ⊗[D.host.F] D.host.E | z ∈ intAE D} := by
      have := isOpen_nsmul_adelicCompletion_integers D.host.F D.host.E 1 one_pos
      rw [← integralFiniteAdeles_eq_adelicCompletion_integers] at this
      convert this using 1
      ext z
      simp
    have c1 : Continuous fun x : (AE D)ˣ => finPart D (x : AE D) := hfc.comp Units.continuous_val
    have c2 : Continuous fun x : (AE D)ˣ => finPart D ((x⁻¹ : (AE D)ˣ) : AE D) :=
      hfc.comp Units.continuous_coe_inv
    have c3 : Continuous fun x : (AE D)ˣ => finPart D (x : AE D) - 1 := by
      simp only [sub_eq_add_neg]
      exact c1.add continuous_const
    exact (h1.preimage c1).inter ((h1.preimage c2).inter (hN'.preimage c3))
  · exact exists_units_parts e hec hes (infPart D) (finPart D) he

end GlobalTheory.IdeleParts
end
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.exists_place_not_pow_adicCompletion : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (ζ u : F) (S₀ : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → u ≠ 0 → (∀ r : F, r ^ p ≠ u) → ∃ v, v ∉ S₀ ∧ ∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) u := by
  first | exact @GlobalTheory.CNorm.exists_not_mem_not_pow_completion | exact GlobalTheory.CNorm.exists_not_mem_not_pow_completion | (intros; apply GlobalTheory.CNorm.exists_not_mem_not_pow_completion <;> assumption)
end
