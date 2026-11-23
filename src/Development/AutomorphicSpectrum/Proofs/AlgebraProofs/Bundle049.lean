module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.WeilBound.CoreStatements.HodgeTatePoints.BilinearPartAx3
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle045
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle046
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle025
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalCharacterIdealPowers
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle044
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterExists
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterOrderGenerates
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle022
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RangeSubtypeEq
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RcFlag
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle013
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle040
public import ReciprocityTheory.DualLattices.IsUnitDetOfSpanEq
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj.Iso

theorem rho_pairing : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (B₂ : FB R d O) (φ ψ : Pt R 1 d) (lam : PS R 2 d), IsIso B B₂ φ ψ lam → lin φ 1 * lin ψ 1 = 1 ∧ lin ψ 1 * lin φ 1 = 1 ∧ Function.Bijective (transH φ ψ lam) ∧ (∀ a, rho B a * lin φ 1 = lin φ 1 * rho B₂ a) ∧ (∀ a, rhoH B a ∘ₗ transH φ ψ lam = transH φ ψ lam ∘ₗ rhoH B₂ a) ∧ ∀ y y', pairH B (transH φ ψ lam y) (transH φ ψ lam y') = pairH B₂ y y' :=
  PositivityTheory.HtPt.Ca.iso_rho

end GlobalTheory.CompanionTheory.Ar.Conj.Iso
end

section

open GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Flat.DegCurve

theorem _root_.GlobalTheory.T.filtered_exact_sequence_projector_bundles : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (V'' : Type) [AddCommGroup V''] [Module K V''] [FiniteDimensional K V''] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'') (f : V →ₗ[K] V') (g : V' →ₗ[K] V'') (P : V →ₗ[K] V) (P' : V' →ₗ[K] V') (P'' : V'' →ₗ[K] V''), IsBun C L' → ShortExact C L L' L'' f g → (∀ x, P (P x) = P x) → (∀ x, P' (P' x) = P' x) → (∀ x, P'' (P'' x) = P'' x) → (∀ x, f (P x) = P' (f x)) → (∀ y, g (P' y) = P'' (g y)) → IsHom C L' L' P' → subDeg C L' (LinearMap.range P') = subDeg C L (LinearMap.range P) + subDeg C L'' (LinearMap.range P'') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.subDeg_range_shortExact | exact GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.subDeg_range_shortExact | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.subDeg_range_shortExact <;> assumption)
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.T.hopf_order_retract_restriction : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'], ∀ (ι : N' →+ N) (π : N →+ N'), (∀ y, π (ι y) = y) → (∀ g ∈ AA.carrier, (fun x => g (ι (π x))) ∈ AA.carrier) → (∃ A' : HopfOrder (C := C) R N', A'.carrier = AA.carrier.map (LinearMap.funLeft R C (ι : N' → N))) ∧ (∀ h ∈ AA.carrier.map (LinearMap.funLeft R C (ι : N' → N)), (fun x => h (π x)) ∈ AA.carrier) ∧ ∀ K' : AddSubgroup N', GenAF p AA.carrier (K'.map ι) → GenAF p (AA.carrier.map (LinearMap.funLeft R C (ι : N' → N))) K' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.ret_hopf_factor | exact GlobalTheory.CompanionTheory.Ar.GR.ret_hopf_factor | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.ret_hopf_factor <;> assumption)
end

section

open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

theorem _root_.GlobalTheory.T.sum_eigen_projections_eq_self : ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C] [Fintype (E →+* C)], Fintype.card (E →+* C) = Module.finrank ℚ E → ∀ (M : Type) [AddCommGroup M] [Module C M] (ρ : 𝓞 E →+* Module.End C M) (y : M), ∑ s, HT.eigProj ρ s y = y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ExG.SumEig.sum_eigProj | exact GlobalTheory.CompanionTheory.Ar.Flat.ExG.SumEig.sum_eigProj | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ExG.SumEig.sum_eigProj <;> assumption)
end

section

open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

theorem _root_.GlobalTheory.T.dual_module_conjugate_eigen_action : ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [Fintype (E →+* C)] (bar : 𝓞 E ≃+* 𝓞 E) (s s' : E →+* C) (W : Type) [AddCommGroup W] [Module C W] [FiniteDimensional C W] (ρ : 𝓞 E →+* Module.End C W) (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W)), (∀ y, ∑ t, HT.eigProj ρ t y = y) → (∀ a : 𝓞 E, s' (a : E) = s (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → Module.finrank C ↥(HT.eigSp ρH s ⊓ LinearMap.ker (LinearMap.fst C W (Module.Dual C W))) = Module.finrank C (HT.eigSp ρ s') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualRank.finrank_eigSp_inf_ker_fst | exact GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualRank.finrank_eigSp_inf_ker_fst | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualRank.finrank_eigSp_inf_ker_fst <;> assumption)
end

section

open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

theorem _root_.GlobalTheory.T.hodge_lattice_dual_eigen_decomposition : ∀ (E : Type) [Field E] [NumberField E] (V C : Type) [CommRing V] [Field C] [Algebra V C] [Fintype (E →+* C)] (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C) (W : Type) [AddCommGroup W] [Module C W] [Module V W] [IsScalarTower V C W] (ρ : 𝓞 E →+* Module.End C W) (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W)) (HV : Submodule V (W × Module.Dual C W)) (Lie : Submodule V W) (n : ℕ) (w : Fin n → W) (ψ : Fin n → W × Module.Dual C W), (∀ y, ∑ s, HT.eigProj ρ s y = y) → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → (∀ φ : Module.Dual C W, (0, φ) ∈ HV ↔ ∀ e ∈ Lie, φ e ∈ (algebraMap V C).range) → Submodule.span C (Set.range w) = HT.eigSp ρ σ' → (∀ j, w j ∈ Lie) → (∀ j, ψ j ∈ HT.eigSp ρH σ ∧ (ψ j).1 = 0 ∧ ∀ j', (ψ j).2 (w j') = if j = j' then 1 else 0) → (∀ j, ∃ φ : Module.Dual C W, (∀ y ∈ Lie, φ y ∈ (algebraMap V C).range) ∧ ∀ k, φ (w k) = if k = j then 1 else 0) → ∀ y, y ∈ Submodule.span V (Set.range ψ) ↔ ∃ φ : Module.Dual C W, ((0, φ) : W × Module.Dual C W) ∈ HV ∧ HT.eigProj ρH σ (0, φ) = y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualFil.span_iff_proj | exact GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualFil.span_iff_proj | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualFil.span_iff_proj <;> assumption)
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR.NonFund

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
  {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N)

theorem aug_mul {g h : N → C} (hg : g ∈ augIdeal AA.carrier) (hh : h ∈ AA.carrier) :
    g * h ∈ augIdeal AA.carrier := by
  refine ⟨AA.mul_mem _ _ hg.1 hh, ?_⟩
  have h0 : g 0 = 0 := hg.2
  change g 0 * h 0 = 0
  rw [h0, zero_mul]

theorem sq_mul {g h : N → C} (hg : g ∈ sqIdeal (augIdeal AA.carrier)) (hh : h ∈ AA.carrier) :
    g * h ∈ sqIdeal (augIdeal AA.carrier) := by
  unfold sqIdeal at hg
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    exact Submodule.subset_span ⟨a, ha, b * h, aug_mul AA hb hh, mul_assoc _ _ _⟩
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

def Lev (k : ℕ) (g : N → C) : Prop :=
  g ∈ AA.carrier ∧ (1 ≤ k → g ∈ augIdeal AA.carrier) ∧
    (2 ≤ k → g ∈ sqIdeal (augIdeal AA.carrier))

theorem lev_one : Lev AA 0 1 :=
  ⟨AA.one_mem, fun h => absurd h (by omega), fun h => absurd h (by omega)⟩

theorem lev_mul {k l : ℕ} {g h : N → C} (hg : Lev AA k g) (hh : Lev AA l h) :
    Lev AA (k + l) (g * h) := by
  refine ⟨AA.mul_mem _ _ hg.1 hh.1, fun hk => ?_, fun hk => ?_⟩
  · by_cases h1 : 1 ≤ k
    · exact aug_mul AA (hg.2.1 h1) hh.1
    · rw [mul_comm]; exact aug_mul AA (hh.2.1 (by omega)) hg.1
  · by_cases h2 : 2 ≤ k
    · exact sq_mul AA (hg.2.2 h2) hh.1
    · by_cases h3 : 2 ≤ l
      · rw [mul_comm]; exact sq_mul AA (hh.2.2 h3) hg.1
      · exact Submodule.subset_span ⟨g, hg.2.1 (by omega), h, hh.2.1 (by omega), rfl⟩

theorem lev_pow {g : N → C} (hg : g ∈ augIdeal AA.carrier) (k : ℕ) : Lev AA k (g ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact lev_one AA
  | succ k ih =>
    rw [pow_succ]
    exact lev_mul AA ih ⟨hg.1, fun _ => hg, fun h => absurd h (by omega)⟩

theorem lev_prod {ι : Type} (s : Finset ι) (u : ι → N → C) (hu : ∀ i, u i ∈ augIdeal AA.carrier)
    (d : ι → ℕ) : Lev AA (∑ i ∈ s, d i) (∏ i ∈ s, u i ^ d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty]; exact lev_one AA
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact lev_mul AA (lev_pow AA (hu a) _) ih

theorem digits_single {f p : ℕ} (d : Fin f → ℕ) (n : Fin f) (hn : d n ≠ 0)
    (hs : ¬ 2 ≤ ∑ i, d i) : ∑ i : Fin f, d i * p ^ (i : ℕ) = p ^ (n : ℕ) := by
  have h := Finset.add_sum_erase Finset.univ d (Finset.mem_univ n)
  have h1 : d n = 1 := by omega
  have h0 : ∑ i ∈ Finset.univ.erase n, d i = 0 := by omega
  rw [Finset.sum_eq_zero_iff] at h0
  rw [Finset.sum_eq_single n, h1, one_mul]
  · intro b _ hb
    rw [h0 b (Finset.mem_erase.2 ⟨hb, Finset.mem_univ b⟩), zero_mul]
  · intro h; exact absurd (Finset.mem_univ n) h

end GlobalTheory.CompanionTheory.Ar.GR.NonFund

open GlobalTheory.CompanionTheory.Ar.GR.NonFund in
theorem _root_.GlobalTheory.CompanionTheory.Relay.non_fundamental_eigen_le_square_augmentation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∀ χ : MulChar F R, ¬ IsFund p χ → eig AA.carrier χ ≤ sqIdeal (augIdeal AA.carrier) := by
  intro p hpp C _ _ _ v R _ _ hv hp F _ _ _ _ f hc AA hA χ hχ g hg
  obtain ⟨σ, hσ⟩ := fund_ex_relay p C v R hv hp F f hc
  obtain ⟨-, hgen, hfund, -, -⟩ := FundGen.main p C v R hv hp F f hc σ hσ
  obtain ⟨m, hm1, hm2, rfl⟩ := hgen χ
  have hr := eig_rank_one p C v R hv hp F f hc AA hA
  choose c hc0 hcx using fun n : ℕ => (hr (σ ^ p ^ n)).1
  have hp0 : 0 < p := hpp.out.pos
  have hlt : m < p ^ f := by
    have := pow_pos hp0 f
    omega
  obtain ⟨d, hd⟩ : ∃ d : Fin f → Fin p, ∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ) = m := by
    refine ⟨finFunctionFinEquiv.symm ⟨m, hlt⟩, ?_⟩
    rw [← finFunctionFinEquiv_apply, Equiv.apply_symm_apply]
  have hne : ∃ n, (d n : ℕ) ≠ 0 := by
    by_contra hcon
    have h0 : ∀ n, (d n : ℕ) = 0 := fun n => by
      by_contra h; exact hcon ⟨n, h⟩
    simp only [h0, zero_mul, Finset.sum_const_zero] at hd
    omega
  have hx := (GlobalTheory.T.fundamental_ideal_frobenius_powers p C v R hv hp F f hc AA hA σ hσ c hcx).2 d hne
  rw [hd] at hx
  have hs : 2 ≤ ∑ n, (d n : ℕ) := by
    by_contra hs
    obtain ⟨n, hn⟩ := hne
    have := digits_single (p := p) (fun n => (d n : ℕ)) n hn hs
    rw [hd] at this
    rw [this] at hχ
    exact hχ (hfund n)
  obtain ⟨c0, hc0m, rfl⟩ := ((hr (σ ^ m)).2 g).1 hg
  rw [hx, Ideal.mem_span_singleton'] at hc0m
  obtain ⟨r, rfl⟩ := hc0m
  let u : Fin f → F → C := fun n a => algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) a)
  have hu : ∀ n, u n ∈ augIdeal AA.carrier := by
    intro n
    have h1 : u n ∈ eig AA.carrier (σ ^ p ^ (n : ℕ)) :=
      ((hr _).2 _).2 ⟨c n, by rw [hcx]; exact Ideal.mem_span_singleton_self _, rfl⟩
    refine ⟨h1.1, ?_⟩
    change algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) 0) = 0
    rw [MulChar.map_zero, mul_zero, map_zero]
  have hprod := (lev_prod AA Finset.univ u hu fun n => (d n : ℕ)).2.2 hs
  convert Submodule.smul_mem _ r hprod using 1
  funext a
  have ha : (σ ^ m) a = ∏ n : Fin f, ((σ ^ p ^ (n : ℕ)) a) ^ (d n : ℕ) := by
    rw [MulChar.pow_apply' _ (by omega), ← hd, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun n _ => ?_
    rw [MulChar.pow_apply' _ (pow_pos hp0 _).ne', ← pow_mul, mul_comm]
  rw [ha, mul_assoc, ← Finset.prod_mul_distrib, map_mul, map_prod, Pi.smul_apply,
    Algebra.smul_def, Finset.prod_apply]
  refine congrArg _ (Finset.prod_congr rfl fun n _ => ?_)
  rw [← mul_pow, map_pow, Pi.pow_apply]
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR.RankOneColen

lemma two_mul_sum_digit (p f : ℕ) (j : Fin f) :
    (∑ d : Fin f → Fin p, (d j : ℕ)) * 2 = p ^ f * (p - 1) := by
  let e : (Fin f → Fin p) ≃ (Fin f → Fin p) := Equiv.arrowCongr (Equiv.refl _) Fin.revPerm
  have h1 : ∑ d : Fin f → Fin p, ((e d) j : ℕ) = ∑ d : Fin f → Fin p, (d j : ℕ) :=
    e.sum_comp (fun d => (d j : ℕ))
  have h2 : ∀ d : Fin f → Fin p, ((e d) j : ℕ) = p - ((d j : ℕ) + 1) := by
    intro d
    simp [e, Equiv.arrowCongr_apply, Fin.val_rev]
  simp only [h2] at h1
  rw [mul_two]
  nth_rewrite 2 [← h1]
  rw [← Finset.sum_add_distrib]
  have h3 : ∀ d : Fin f → Fin p, (d j : ℕ) + (p - ((d j : ℕ) + 1)) = p - 1 := by
    intro d; have := (d j).2; omega
  simp only [h3, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul]

lemma prod_digit_sq (p f : ℕ) (x : Fin f → NNReal) :
    (∏ d : Fin f → Fin p, ∏ j, x j ^ (d j : ℕ)) ^ 2 = (∏ j, x j) ^ (p ^ f * (p - 1)) := by
  have key : ∀ j : Fin f, (∏ d : Fin f → Fin p, x j ^ (d j : ℕ)) ^ 2 = x j ^ (p ^ f * (p - 1)) := by
    intro j
    rw [Finset.prod_pow_eq_pow_sum, ← pow_mul, two_mul_sum_digit]
  calc (∏ d : Fin f → Fin p, ∏ j, x j ^ (d j : ℕ)) ^ 2
      = (∏ j, ∏ d : Fin f → Fin p, x j ^ (d j : ℕ)) ^ 2 := by rw [Finset.prod_comm]
    _ = ∏ j, (∏ d : Fin f → Fin p, x j ^ (d j : ℕ)) ^ 2 := (Finset.prod_pow _ _ _).symm
    _ = ∏ j, x j ^ (p ^ f * (p - 1)) := Finset.prod_congr rfl (fun j _ => key j)
    _ = (∏ j, x j) ^ (p ^ f * (p - 1)) := Finset.prod_pow _ _ _

def num {p f : ℕ} (d : Fin f → Fin p) : ℕ := ∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ)

lemma num_eq {p f : ℕ} (d : Fin f → Fin p) : num d = (finFunctionFinEquiv d : ℕ) := by
  rw [num, finFunctionFinEquiv_apply]

lemma num_lt {p f : ℕ} (d : Fin f → Fin p) : num d < p ^ f := by
  rw [num_eq]; exact Fin.isLt _

lemma num_inj {p f : ℕ} {d e : Fin f → Fin p} (h : num d = num e) : d = e := by
  rw [num_eq, num_eq] at h
  exact finFunctionFinEquiv.injective (Fin.ext h)

lemma num_surj {p f m : ℕ} (h : m < p ^ f) : ∃ d : Fin f → Fin p, num d = m :=
  ⟨finFunctionFinEquiv.symm ⟨m, h⟩, by rw [num_eq, Equiv.apply_symm_apply]⟩

lemma num_ne_zero_iff {p f : ℕ} (hp : 0 < p) (d : Fin f → Fin p) :
    num d ≠ 0 ↔ ∃ n, (d n : ℕ) ≠ 0 := by
  constructor
  · intro h
    by_contra hc
    have hc' : ∀ n, (d n : ℕ) = 0 := fun n => by_contra (fun hn => hc ⟨n, hn⟩)
    apply h
    simp [num, hc']
  · rintro ⟨n, hn⟩ h
    apply hn
    rw [num] at h
    have h' := (Finset.sum_eq_zero_iff.mp h) n (Finset.mem_univ _)
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact h''
    · exact absurd h'' (pow_ne_zero _ hp.ne')

lemma prod_Icc_num {M : Type} [CommMonoid M] {p f : ℕ} (hp : 0 < p) (g : ℕ → M)
    (G : (Fin f → Fin p) → M) (h0 : ∀ d, num d = 0 → G d = 1)
    (h1 : ∀ d, num d ≠ 0 → g (num d) = G d) :
    ∏ m ∈ Finset.Icc 1 (p ^ f - 1), g m = ∏ d, G d := by
  classical
  have hfilt : ∏ d ∈ Finset.univ.filter (fun d : Fin f → Fin p => num d ≠ 0), G d = ∏ d, G d :=
    Finset.prod_filter_of_ne (fun d _ hG h0' => hG (h0 d h0'))
  rw [← hfilt]
  symm
  refine Finset.prod_bij (fun d _ => num d) ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    have := num_lt d
    rw [Finset.mem_Icc]
    omega
  · intro a _ b _ h
    exact num_inj h
  · intro m hm
    rw [Finset.mem_Icc] at hm
    obtain ⟨d, hd⟩ := num_surj (p := p) (f := f) (show m < p ^ f by omega)
    refine ⟨d, ?_, hd⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    exact (h1 d hd).symm

lemma mono_eq {C R F : Type} [Field C] [CommRing R] [Algebra R C] [Field F] {p f : ℕ}
    (hp : 0 < p) (σ : MulChar F R) (c : ℕ → R) (d : Fin f → Fin p) (hd : num d ≠ 0) (a : F) :
    ∏ n : Fin f, algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) a) ^ (d n : ℕ) =
      algebraMap R C ((∏ n : Fin f, c n ^ (d n : ℕ)) * (σ ^ num d) a) := by
  have hpow' : ∀ n : ℕ, (σ ^ p ^ n) a = σ a ^ p ^ n :=
    fun n => MulChar.pow_apply' σ (pow_ne_zero _ hp.ne') a
  rw [MulChar.pow_apply' σ hd a]
  simp only [hpow']
  simp only [map_mul, map_pow, map_prod]
  simp only [mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum, num]
  congr 2
  exact Finset.sum_congr rfl (fun n _ => Nat.mul_comm _ _)

lemma digits_zero {p f : ℕ} (hp : 0 < p) {d : Fin f → Fin p} (hd : num d = 0) (n : Fin f) :
    (d n : ℕ) = 0 := by
  by_contra h
  exact (num_ne_zero_iff hp d).2 ⟨n, h⟩ hd

end GlobalTheory.CompanionTheory.Ar.GR.RankOneColen


open GlobalTheory.CompanionTheory.Ar.GR.RankOneColen in
theorem _root_.GlobalTheory.CompanionTheory.Relay.fundamental_ideal_frobenius_valuation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ c : ℕ → R, (∀ n, xIdeal AA.carrier (σ ^ p ^ n) = Ideal.span {c n}) → AA.carrier = Submodule.span R (Set.range fun (d : Fin f → Fin p) (a : F) => ∏ n : Fin f, algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) a) ^ (d n : ℕ)) ∧ ∀ cN, HasColen R v AA.carrier cN → cN ^ 2 = (∏ n : Fin f, v (algebraMap R C (c n))) ^ (p ^ f * (p - 1)) := by
  intro p _ C _ _ _ v R _ _ hv hpv F _ _ _ _ f hcard AA hst σ hσ c hc
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hT := GlobalTheory.T.fundamental_ideal_frobenius_powers p C v R hv hpv F f hcard AA hst σ hσ c hc
  obtain ⟨c', hc', hc'd⟩ : ∃ c' : ℕ → R, (∀ m, xIdeal AA.carrier (σ ^ m) = Ideal.span {c' m}) ∧
      ∀ d : Fin f → Fin p, num d ≠ 0 → c' (num d) = ∏ n : Fin f, c n ^ (d n : ℕ) := by
    refine ⟨fun m => if h : m ≠ 0 ∧ m < p ^ f then
        ∏ n : Fin f, c n ^ ((Classical.choose (num_surj h.2) : Fin f → Fin p) n : ℕ)
      else Classical.choose (eig_rank_one p C v R hv hpv F f hcard AA hst (σ ^ m)).1, ?_, ?_⟩
    · intro m
      dsimp only
      by_cases h : m ≠ 0 ∧ m < p ^ f
      · rw [dite_eq_left h]
        have hd := Classical.choose_spec (num_surj h.2)
        have hne : ∃ n, ((Classical.choose (num_surj h.2) : Fin f → Fin p) n : ℕ) ≠ 0 :=
          (num_ne_zero_iff hp _).mp (by rw [hd]; exact h.1)
        have e : σ ^ m = σ ^ num (Classical.choose (num_surj h.2)) := by rw [hd]
        rw [e]
        exact hT.2 _ hne
      · rw [dite_eq_right h]
        exact (Classical.choose_spec (eig_rank_one p C v R hv hpv F f hcard AA hst (σ ^ m)).1).2
    · intro d hd
      dsimp only
      have h : num d ≠ 0 ∧ num d < p ^ f := ⟨hd, num_lt d⟩
      rw [dite_eq_left h]
      have := num_inj (Classical.choose_spec (num_surj h.2))
      rw [this]
  obtain ⟨hAug, hCar, hCol⟩ := r_decomp_relay p C v R hv hpv F f hcard AA hst σ hσ c' hc'
  refine ⟨?_, ?_⟩
  · have hset : Set.range (fun (d : Fin f → Fin p) (a : F) =>
          ∏ n : Fin f, algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) a) ^ (d n : ℕ)) =
        insert 1 ((fun m a => algebraMap R C (c' m * (σ ^ m) a)) '' ↑(Finset.Icc 1 (p ^ f - 1))) := by
      ext g
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_image, Finset.coe_Icc, Set.mem_Icc]
      constructor
      · rintro ⟨d, rfl⟩
        by_cases h0 : num d = 0
        · left
          funext a
          simp only [Pi.one_apply]
          exact Finset.prod_eq_one (fun n _ => by rw [digits_zero hp h0 n, pow_zero])
        · right
          refine ⟨num d, ⟨by omega, by have := num_lt d; omega⟩, ?_⟩
          funext a
          rw [mono_eq hp σ c d h0 a, hc'd d h0]
      · rintro (rfl | ⟨m, ⟨hm1, hm2⟩, rfl⟩)
        · refine ⟨fun _ => ⟨0, hp⟩, ?_⟩
          funext a
          simp only [Pi.one_apply]
          exact Finset.prod_eq_one (fun n _ => pow_zero _)
        · obtain ⟨d, rfl⟩ := num_surj (p := p) (f := f) (show m < p ^ f by omega)
          have h0 : num d ≠ 0 := by omega
          refine ⟨d, ?_⟩
          funext a
          rw [mono_eq hp σ c d h0 a, hc'd d h0]
    rw [hset, Submodule.span_insert, ← hAug, ← hCar]
  · intro cN hcN
    have huniq : cN = ∏ m ∈ Finset.Icc 1 (p ^ f - 1), v (algebraMap R C (c' m)) := by
      obtain ⟨B, hB, hBd⟩ := hcN
      obtain ⟨B', hB', hB'd⟩ := hCol
      obtain ⟨P, hPu, hP⟩ := AA.lat
      rw [← hBd, ← hB'd, valuation_det_eq_of_span_eq_alt hv hPu (hP.symm.trans hB),
        valuation_det_eq_of_span_eq_alt hv hPu (hP.symm.trans hB')]
    rw [huniq, prod_Icc_num hp (fun m => v (algebraMap R C (c' m)))
      (fun d => ∏ n : Fin f, v (algebraMap R C (c n)) ^ (d n : ℕ)) ?_ ?_]
    · exact prod_digit_sq p f (fun n => v (algebraMap R C (c n)))
    · intro d hd
      exact Finset.prod_eq_one (fun n _ => by rw [digits_zero hp hd n, pow_zero])
    · intro d hd
      simp only [hc'd d hd, map_prod, map_pow]
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.T.hopf_orders_of_zmod_p_extremes : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → (∃ AA : HopfOrder (C := C) R (ZMod p), AA.carrier = intFun R (ZMod p) ∧ FStable (ZMod p) AA.carrier ∧ IsTight v p AA.carrier ∧ ∀ K, GenAF p AA.carrier K) ∧ (∃ AA : HopfOrder (C := C) R (ZMod p), AA.carrier = Submodule.span R (Set.range fun (ψ : AddChar (ZMod p) C) (x : ZMod p) => ψ x) ∧ AA.carrier ≠ intFun R (ZMod p) ∧ FStable (ZMod p) AA.carrier ∧ IsTight v p AA.carrier ∧ ∀ K, GenAF p AA.carrier K) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.hopf_orders_of_zmod_p_extremes | exact GlobalTheory.CompanionTheory.Relay.hopf_orders_of_zmod_p_extremes | (intros; apply GlobalTheory.CompanionTheory.Relay.hopf_orders_of_zmod_p_extremes <;> assumption)
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.T.stable_hopf_order_subgroup_restriction : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) [Fintype K] [DecidableEq K] [Fintype (N ⧸ K)] [DecidableEq (N ⧸ K)], (∃ AK : HopfOrder (C := C) R K, AK.carrier = (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K → N))) ∧ FStable F AK.carrier) ∧ (∃ AQ : HopfOrder (C := C) R (N ⧸ K), AQ.carrier = (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))) ∧ FStable F AQ.carrier) ∧ invFun AA.carrier K.toAddSubgroup = (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))).map (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K)) ∧ ∀ c cQ cK, HasColen R v AA.carrier c → HasColen R v (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))) cQ → HasColen R v (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K → N))) cK → c = cQ ^ Fintype.card K * cK ^ Fintype.card (N ⧸ K) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.subquoHopfOrder | exact GlobalTheory.CompanionTheory.Ar.GR.subquoHopfOrder | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.subquoHopfOrder <;> assumption)
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.T.stable_hopf_order_subgroup_translation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable (F := F) AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → (∃ S : HopfOrder (C := C) R F, S.carrier = stepOrder AA.carrier K t ∧ FStable (F := F) S.carrier) ∧ stepOrder AA.carrier K t = stepOrderRes AA.carrier K t :=
  @_root_.PositivityTheory.HtPt.Rc.step
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem flag_colen : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (cs : Fin n → NNReal) (cN : NNReal), (∀ i : Fin n, HasColen R v (stepOrder AA.carrier (flagSub b i) (b i)) (cs i)) → HasColen R v AA.carrier cN → cN ^ (p ^ f) = (∏ i, cs i) ^ Fintype.card N :=
  @PositivityTheory.HtPt.Rc.flag_colen

end GlobalTheory.CompanionTheory.Ar.GR
end
