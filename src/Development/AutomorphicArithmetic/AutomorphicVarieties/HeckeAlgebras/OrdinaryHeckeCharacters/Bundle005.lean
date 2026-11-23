module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle001
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle002
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem sphC_fin {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {K : Subgroup G} (hL : IsCompact (K : Set G)) (hK' : IsOpen (K : Set G)) (x : G) :
    (MulAction.orbit K (x : G ⧸ K)).Finite := by
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hK'
  have hc : Continuous fun g : G => ((g * x : G) : G ⧸ K) :=
    QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)
  refine ((hL.image hc).finite_of_discrete).subset ?_
  rintro _ ⟨g, rfl⟩
  exact ⟨g, g.2, rfl⟩

private theorem sphC_le {H : Type} [Group H] (K : Subgroup H) (θ : H →* H) (hθ : ∀ x, θ (θ x) = x)
    (hK : ∀ k ∈ K, θ k ∈ K) (hd : ∀ x, ∃ k ∈ K, ∃ k' ∈ K, θ x⁻¹ = k * x * k')
    (hfin : ∀ x : H, (MulAction.orbit K (x : H ⧸ K)).Finite) (x : H) :
    (MulAction.orbit K (x : H ⧸ K)).ncard ≤ (MulAction.orbit K ((x⁻¹ : H) : H ⧸ K)).ncard := by
  refine Set.ncard_le_ncard_of_injOn (fun q => ((θ q.out : H) : H ⧸ K)) ?_ ?_ (hfin _)
  · rintro q ⟨a, ha⟩
    have h : (((a : H) * x : H) : H ⧸ K) = (q.out : H ⧸ K) := by
      rw [QuotientGroup.out_eq']; exact ha
    have h1 := hK _ (QuotientGroup.eq.mp h)
    obtain ⟨l, hl, l', hl', h2⟩ := hd x⁻¹
    rw [inv_inv] at h2
    refine ⟨⟨θ a * l, mul_mem (hK _ a.2) hl⟩, ?_⟩
    change ((θ a * l * x⁻¹ : H) : H ⧸ K) = _
    refine QuotientGroup.eq.mpr ?_
    have h3 : (θ a * l * x⁻¹)⁻¹ * θ q.out = l' * θ (((a : H) * x)⁻¹ * q.out) := by
      rw [map_mul, map_inv, map_mul, h2]; group
    rw [h3]
    exact mul_mem hl' h1
  · intro p _ q _ h
    have h1 := hK _ (QuotientGroup.eq.mp h)
    rw [← map_inv, ← map_mul, hθ] at h1
    rw [← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' q]
    exact QuotientGroup.eq.mpr h1

private theorem sphC_central {A H M : Type} [CommRing A] [Group H] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (K : Subgroup H) (z : H) (hz : ∀ g, g * z = z * g) (v : M) (hv : v ∈ fixd ρ K) :
    dc ρ K K z v = ρ z v := by
  have ho : MulAction.orbit K (z : H ⧸ K) = {(z : H ⧸ K)} := by
    ext q
    constructor
    · rintro ⟨a, rfl⟩
      change (((a : H) * z : H) : H ⧸ K) = _
      rw [hz]
      exact QuotientGroup.eq.mpr (by simp)
    · rintro rfl
      exact MulAction.mem_orbit_self _
  rw [dc, finsum_set_coe_eq_finsum_mem (f := fun q : H ⧸ K => ρ q.out), ho, finsum_mem_singleton]
  obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul K z
  rw [hm, map_mul, Module.End.mul_apply, hv m m.2]

private theorem sphC_invT {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (g : GL (Fin n) k) (hg : g ∈ KO k (Fin n)) : GlobalTheory.CuspRep.invT n k g ∈ KO k (Fin n) := by
  rw [GlobalTheory.SplitFlip.mem_KO_iff] at hg ⊢
  exact ⟨fun i j => hg.2 j i, fun i j => hg.1 j i⟩

private theorem sphC_cartan {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (g : GL (Fin n) k) :
    ∃ a ∈ KO k (Fin n), ∃ b ∈ KO k (Fin n), GlobalTheory.CuspRep.invT n k g⁻¹ = a * g * b := by
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors 𝒪[k])
    (fun p : Fin n × Fin n => g.val p.1 p.2)
  choose f hf using hc
  obtain ⟨U, V, d, hU, hV, hΦ, -⟩ := KStar.Selmer.exists_smith n (Matrix.of fun i j => f (i, j))
  obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det U).2 hU
  obtain ⟨w, rfl⟩ := (Matrix.isUnit_iff_isUnit_det V).2 hV
  set u' : GL (Fin n) k := Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u with hu'
  set w' : GL (Fin n) k := Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) w with hw'
  have hu : u' ∈ KO k (Fin n) := ⟨u, rfl⟩
  have hw : w' ∈ KO k (Fin n) := ⟨w, rfl⟩
  have hc0 : algebraMap 𝒪[k] k c ≠ 0 := fun h =>
    nonZeroDivisors.ne_zero c.2 (Subtype.ext h)
  have h1 : algebraMap 𝒪[k] k c • g.val =
      u'.val * Matrix.diagonal (fun i => algebraMap 𝒪[k] k (d i)) * w'.val := by
    have h2 := congrArg (algebraMap 𝒪[k] k).mapMatrix hΦ
    rw [map_mul, map_mul, RingHom.mapMatrix_apply (M := Matrix.diagonal d), Matrix.diagonal_map (map_zero _)] at h2
    refine Eq.trans ?_ h2
    ext i j
    exact (hf (i, j)).symm
  have h3 : algebraMap 𝒪[k] k c • (u'⁻¹ * g * w'⁻¹).val = Matrix.diagonal (fun i => algebraMap 𝒪[k] k (d i)) := by
    rw [Units.val_mul, Units.val_mul, ← smul_mul_assoc, ← mul_smul_comm, h1]
    simp only [← mul_assoc, Units.inv_mul, one_mul]
    rw [mul_assoc, Units.mul_inv, mul_one]
  have h4 : GlobalTheory.CuspRep.invT n k (u'⁻¹ * g * w'⁻¹)⁻¹ = u'⁻¹ * g * w'⁻¹ := by
    apply Units.ext
    change (u'⁻¹ * g * w'⁻¹).val.transpose = _
    apply smul_right_injective _ hc0
    simp only
    rw [← Matrix.transpose_smul, h3, Matrix.diagonal_transpose]
  refine ⟨GlobalTheory.CuspRep.invT n k w'⁻¹ * u'⁻¹, mul_mem (sphC_invT _ (inv_mem hw)) (inv_mem hu),
    w'⁻¹ * GlobalTheory.CuspRep.invT n k u'⁻¹, mul_mem (inv_mem hw) (sphC_invT _ (inv_mem hu)), ?_⟩
  have h5 : g⁻¹ = w'⁻¹ * (u'⁻¹ * g * w'⁻¹)⁻¹ * u'⁻¹ := by group
  rw [h5, map_mul, map_mul, h4]
  simp only [mul_assoc]

theorem UpperTheory.V.Hi.sphComm :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M), (∀ x : GL (Fin n) k, (MulAction.orbit (KO k (Fin n)) (x : GL (Fin n) k ⧸ KO k (Fin n))).Finite) ∧ (∀ x y, ∀ v ∈ fixd ρ (KO k (Fin n)), dc ρ (KO k (Fin n)) (KO k (Fin n)) x (dc ρ (KO k (Fin n)) (KO k (Fin n)) y v) = dc ρ (KO k (Fin n)) (KO k (Fin n)) y (dc ρ (KO k (Fin n)) (KO k (Fin n)) x v)) ∧ ∀ v ∈ fixd ρ (KO k (Fin n)), sphOp ρ 0 v = v ∧ sphOp ρ n v = ρ (al k n n) v := by
  intro k _ _ _ _ n A M _ _ _ ρ
  have hfin : ∀ x : GL (Fin n) k, (MulAction.orbit (KO k (Fin n)) (x : GL (Fin n) k ⧸ KO k (Fin n))).Finite :=
    sphC_fin GlobalTheory.SplitFlip.isCompact_KO GlobalTheory.SplitFlip.isOpen_KO
  have hθ : ∀ x, GlobalTheory.CuspRep.invT n k (GlobalTheory.CuspRep.invT n k x) = x := fun x => Units.ext rfl
  have hle := sphC_le (KO k (Fin n)) (GlobalTheory.CuspRep.invT n k) hθ sphC_invT sphC_cartan hfin
  refine ⟨hfin, ?_, fun v hv => ⟨?_, ?_⟩⟩
  · refine dcGelfand A _ M ρ _ (fun x => GlobalTheory.CuspRep.invT n k x⁻¹) ?_ ?_ ?_ sphC_cartan hfin ?_
    · intro x y
      rw [mul_inv_rev, map_mul]
    · intro x
      rw [← map_inv, inv_inv, hθ]
    · intro a ha
      exact sphC_invT _ (inv_mem ha)
    · intro x
      refine le_antisymm (hle x) ?_
      simpa using hle x⁻¹
  · have h1 : al k n 0 = 1 := by
      rw [al, upow, ← (diagT k (Fin n)).map_one]
      congr 1
      funext i
      simp
    rw [sphOp, h1, sphC_central ρ _ 1 (by simp) v hv, map_one, Module.End.one_apply]
  · refine sphC_central ρ _ _ (fun g => Units.ext ?_) v hv
    have h1 : (al k n n).val = Matrix.scalar (Fin n) (unif k : k) := by
      rw [al, upow, val_diagT, Matrix.scalar_apply]
      congr 1
      funext i
      simp [i.isLt]
    rw [Units.val_mul, Units.val_mul, h1]
    exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq.symm
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem satT_dc {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K : Subgroup G) (a : G) (hf : (MulAction.orbit K (a : G ⧸ K)).Finite) (S : Set G)
    (hS : ∀ g, g ∈ S ↔ ∃ x ∈ K, ∃ y ∈ K, g = x * a * y) (v : V) :
    dc ρ K K a v = GlobalTheory.LFun.heckeVec ρ K (Set.indicator S 1) v := by
  classical
  haveI := hf.to_subtype
  have h1 : dc ρ K K a v = ∑ᶠ q : MulAction.orbit K (a : G ⧸ K), ρ (q : G ⧸ K).out v :=
    (LinearMap.applyₗ (R := ℂ) (M₂ := V) v).toAddMonoidHom.map_finsum (Set.toFinite _)
  rw [h1, finsum_set_coe_eq_finsum_mem (f := fun c : G ⧸ K => ρ c.out v), finsum_mem_def, GlobalTheory.LFun.heckeVec]
  refine finsum_congr fun c => ?_
  have h2 : c ∈ MulAction.orbit K (a : G ⧸ K) ↔ c.out ∈ S := by
    rw [hS]
    constructor
    · rintro ⟨x, hx⟩
      have hx' : ((x.1 * a : G) : G ⧸ K) = (c.out : G ⧸ K) := hx.trans c.out_eq'.symm
      exact ⟨x, x.2, _, QuotientGroup.eq.1 hx', by group⟩
    · rintro ⟨x, hx, y, hy, e⟩
      refine ⟨⟨x, hx⟩, ?_⟩
      change ((x * a : G) : G ⧸ K) = c
      rw [← c.out_eq', e]
      exact (QuotientGroup.mk_mul_of_mem _ hy).symm
  by_cases hc : c.out ∈ S
  · rw [Set.indicator_of_mem hc, Set.indicator_of_mem (h2.2 hc)]; simp
  · rw [Set.indicator_of_notMem hc, Set.indicator_of_notMem (mt h2.1 hc)]; simp

private theorem satT_unif (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) :
    Formalism.UG.IsUnifV L w (unif (w.adicCompletion L) : w.adicCompletion L) := by
  haveI : (Valued.v : Valuation (w.adicCompletion L) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := ValuativeRel.isEquiv (valuation (w.adicCompletion L))
    (Valued.v : Valuation (w.adicCompletion L) (WithZero (Multiplicative ℤ)))
  have hu : valuation (w.adicCompletion L) (unif (w.adicCompletion L) : w.adicCompletion L) =
      uniformizer (w.adicCompletion L) := by
    refine Classical.epsilon_spec (p := fun x : (w.adicCompletion L)ˣ =>
      valuation (w.adicCompletion L) (x : w.adicCompletion L) = uniformizer (w.adicCompletion L)) ?_
    obtain ⟨x, hx⟩ := valuation_surjective (uniformizer (w.adicCompletion L))
    refine ⟨Units.mk0 x ?_, hx⟩
    rintro rfl
    exact (zero_lt_iff.2 (by simp) : 0 < uniformizer (w.adicCompletion L)).ne ((map_zero _).symm.trans hx)
  obtain ⟨p, hp⟩ := GlobalTheory.LFun.exists_isUnifV w
  unfold Formalism.UG.IsUnifV at hp ⊢
  have h1 : Valued.v (unif (w.adicCompletion L) : w.adicCompletion L) < (1 : WithZero (Multiplicative ℤ)) :=
    he.lt_one_iff_lt_one.1 (hu.trans_lt uniformizer_lt_one)
  have h2 : valuation (w.adicCompletion L) p < 1 := he.lt_one_iff_lt_one.2 (by rw [hp]; decide)
  have h3 := (he _ _).1 ((le_uniformizer_iff.2 h2).trans_eq hu.symm)
  rw [hp] at h3
  refine le_antisymm ?_ h3
  change _ ≤ WithZero.exp (-1 : ℤ)
  rw [← WithZero.lt_mul_exp_iff_le (by simp), ← WithZero.exp_add]
  simpa using h1

private theorem satT_num (q n j : ℕ) (hq : q ≠ 0) :
    ((((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ)) ^ j =
      (q : ℂ) ^ (j * (j - 1) / 2) * (q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2) := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have h2 : ((j * (j - 1) / 2 : ℕ) : ℂ) = (j : ℂ) * ((j : ℂ) - 1) / 2 := by
    rw [← Nat.choose_two_right, Nat.cast_choose_two]
  rw [Complex.ofReal_cpow (Nat.cast_nonneg q), ← Complex.cpow_nat_mul, ← Complex.cpow_natCast, h2]
  push_cast
  rw [← Complex.cpow_add _ _ hq']
  congr 1
  ring

private theorem satT_pol (q n : ℕ) (hq : q ≠ 0) (B : Multiset ℂˣ) (hB : B.card = n) (a : ℕ → ℂ)
    (ha : ∀ j ≤ n, a j = GlobalTheory.LFun.satEig q n B j) :
    ((UpperTheory.V.Af.algSat n q B).map fun b => X - C b).prod = heckePol n q a := by
  have hc : (UpperTheory.V.Af.algSat n q B).card = n := by simp [UpperTheory.V.Af.algSat, hB]
  rw [Multiset.prod_X_sub_X_eq_sum_esymm, hc, UpperTheory.V.Hi.heckePol]
  refine Finset.sum_congr rfl fun j hj => ?_
  have e : (UpperTheory.V.Af.algSat n q B).esymm j =
      ((((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ)) ^ j * (B.map fun b : ℂˣ => (b : ℂ)).esymm j := by
    rw [← smul_eq_mul, Multiset.pow_smul_esymm, UpperTheory.V.Af.algSat]
    congr 2
    simp
  rw [ha j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)), e, satT_num q n j hq, GlobalTheory.LFun.satEig]
  simp only [map_mul, map_pow, map_neg, map_one]
  ring

theorem UpperTheory.V.Hi.satT :
    ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (w : HeightOneSpectrum (𝓞 L)) (σ : SmIrr (GL (Fin n) (w.adicCompletion L))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B → GlobalTheory.LFun.KGL w (n := n) = KO (w.adicCompletion L) (Fin n) ∧ ∃ a : ℕ → ℂ, a 0 = 1 ∧ (∀ j, ∀ v ∈ fixd σ.ρ (KO (w.adicCompletion L) (Fin n)), sphOp σ.ρ j v = a j • v) ∧ ((UpperTheory.V.Af.algSat n (normV w) B).map fun b => X - C b).prod = heckePol n (normV w) a := by
  intro L _ _ n w σ B hB
  have hK : KO (w.adicCompletion L) (Fin n) = GlobalTheory.LFun.KGL w (n := n) := GlobalTheory.SmGL.SphCompletion.KO_completion w n
  have hq : Formalism.UG.qV L w = normV w := by
    simp [normV, Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  refine ⟨hK.symm, fun j => GlobalTheory.LFun.satEig (normV w) n B (min j n), by simp [GlobalTheory.LFun.satEig, Multiset.esymm], ?_,
    satT_pol (normV w) n (hq ▸ GlobalTheory.LFun.qV_ne_zero w) B hB.card
      (fun j => GlobalTheory.LFun.satEig (normV w) n B (min j n)) (fun j hj => by rw [min_eq_left hj])⟩
  intro j v hv
  by_cases h0 : v = 0
  · simp [h0]
  rw [hK] at hv
  have h1 := (hB.2 v (GlobalTheory.LGrp.mem_fixed.2 hv) h0).2.2.2 _ (satT_unif L w) (min j n) (min_le_right _ _)
  rw [hq] at h1
  refine Eq.trans ?_ h1
  rw [sphOp, hK]
  refine satT_dc σ.ρ _ _ (Formalism.UG.P.orbit_coset_finite _ (Formalism.UG.Final.GLintComm L w n) _) _ (fun g => ?_) v
  have hal : (al (w.adicCompletion L) n j).val =
      Formalism.UG.diagJ n (unif (w.adicCompletion L) : w.adicCompletion L) (min j n) := by
    rw [UpperTheory.V.Hi.al, upow, val_diagT, Formalism.UG.diagJ]
    congr 1
    funext i
    have := i.2
    by_cases h : (i : ℕ) < j
    · simp [h]
    · simp [h]
  simp only [Set.mem_setOf_eq, ← hal, ← Units.val_mul, Units.val_inj]
end
