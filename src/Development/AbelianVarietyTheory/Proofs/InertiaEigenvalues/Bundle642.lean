module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKummerField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle044
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle199
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle091
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
public import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeAndRangePowLe
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Kernel
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle613
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeExpansionsStdBelowLevel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle612
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle593

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocLanglands

namespace GlobalTheory.DelEps.Twist

section Local

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def filtSub (a : ℕ) : Subgroup kˣ where
  carrier := unitFilt k a
  one_mem' := ⟨by simp, by simp⟩
  mul_mem' := fun {x y} hx hy => ⟨by rw [Units.val_mul, map_mul, hx.1, hy.1, one_mul], by
    have e : ((x * y : kˣ) : k) - 1 = (x : k) * ((y : k) - 1) + ((x : k) - 1) := by rw [Units.val_mul]; ring
    rw [e]
    refine Valuation.map_add_le _ ?_ hx.2
    rw [map_mul, hx.1, one_mul]
    exact hy.2⟩
  inv_mem' := fun {x} hx => by
    have h1 : valuation k ((x⁻¹ : kˣ) : k) = 1 := by rw [Units.val_inv_eq_inv_val, map_inv₀, hx.1, inv_one]
    refine ⟨h1, ?_⟩
    have e : ((x⁻¹ : kˣ) : k) - 1 = -(((x⁻¹ : kˣ) : k) * ((x : k) - 1)) := by
      linear_combination x.inv_mul
    rw [e, Valuation.map_neg, map_mul, h1, one_mul]
    exact hx.2

theorem isOpen_filtSub (a : ℕ) : IsOpen (filtSub k a : Set kˣ) :=
  (GroundTheory.LocalField.isOpen_setOf_valuation_eq_one.inter (GroundTheory.LocalField.isOpen_setOf_valuation_sub_le (a := (1 : k))
    (pow_ne_zero a uniformizer_ne_zero))).preimage Units.continuous_val

theorem ord_zpow (p : kˣ) (n : ℤ) : ord k (p ^ n) = n * ord k p := by
  let f : kˣ →* Multiplicative ℤ :=
    { toFun := fun x => Multiplicative.ofAdd (ord k x)
      map_one' := by rw [ord_eq_zero (by simp)]; rfl
      map_mul' := fun x y => by rw [ord_mul]; rfl }
  have := congrArg Multiplicative.toAdd (map_zpow f p n)
  simpa [f] using this

end Local

section Global

open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {k : Type} [Field k] [NumberField k]

def comp (w : HeightOneSpectrum (𝓞 k)) : Ideles k →* (w.adicCompletion k)ˣ :=
  Units.map
    { toFun := fun a : AdeleRing (𝓞 k) k => a.2 w
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

theorem continuous_comp (w : HeightOneSpectrum (𝓞 k)) : Continuous (comp w) :=
  Continuous.units_map _ ((RestrictedProduct.continuous_eval w).comp continuous_snd)

theorem comp_diag (w : HeightOneSpectrum (𝓞 k)) (x : kˣ) : comp w (diagUnits k x) = atFin w x := Units.ext rfl

theorem comp_local_self (w : HeightOneSpectrum (𝓞 k)) (x : (w.adicCompletion k)ˣ) : comp w (localIdele k w x) = x :=
  Units.ext (localIdele_snd_self k w x)

theorem comp_local_ne {w w' : HeightOneSpectrum (𝓞 k)} (h : w' ≠ w) (x : (w.adicCompletion k)ˣ) :
    comp w' (localIdele k w x) = 1 :=
  Units.ext ((localIdele_isSupportedAt k w x).2 w' h)

theorem comp_inf (w : HeightOneSpectrum (𝓞 k)) (u : InfinitePlace k) (x : (u.Completion)ˣ) : comp w (infIdele k u x) = 1 :=
  Units.ext rfl

theorem exists_hchar_prescribed (k : Type) [Field k] [NumberField k] (S : Finset (HeightOneSpectrum (𝓞 k)))
    (θ : ∀ w : HeightOneSpectrum (𝓞 k), (w.adicCompletion k)ˣ →* ℂˣ) (hs : ∀ w ∈ S, IsSmoothChar (θ w))
    (hf : ∀ w ∈ S, ∃ N : ℕ, 0 < N ∧ θ w ^ N = 1) :
    ∃ η : HChar k, (∃ n : ℕ, 0 < n ∧ η.OrderDvd n) ∧ (∀ u : InfinitePlace k, η.locInf u = 1) ∧ ∀ w ∈ S, η.loc w = θ w := by
  classical
  choose! N hN0 hN using hf
  have hm0 : 0 < ∏ w ∈ S, N w := Finset.prod_pos hN0
  have hm : ∀ w ∈ S, ∀ x, θ w x ^ (∏ w ∈ S, N w) = 1 := fun w hw x => by
    obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem N hw
    rw [hd, pow_mul, ← MonoidHom.pow_apply, hN w hw, MonoidHom.one_apply, one_pow]
  set m := ∏ w ∈ S, N w
  obtain ⟨T, hST, hT⟩ := GlobalTheory.ChevalleySUnits.exists_places k S m hm0
  let U : Subgroup (Ideles k) := GlobalTheory.LevelChars.levSub k T 1 ⊓ ⨅ w : S, (θ w).ker.comap (comp w.1)
  have hU : IsOpen (U : Set (Ideles k)) := by
    have h1 : IsOpen (GlobalTheory.LevelChars.levSub k T 1 : Set (Ideles k)) := by
      convert (GlobalTheory.Mem.UnitOpen.unit_open_and_congr_open k).2 T 1 using 1
      ext a
      exact ⟨fun h => ⟨fun v => (h v).1, fun v hv => (h v).2 hv⟩, fun h v => ⟨h.1 v, h.2 v⟩⟩
    rw [Subgroup.coe_inf, Subgroup.coe_iInf]
    exact h1.inter (isOpen_iInter_of_finite fun w => (hs w w.2).preimage (continuous_comp w.1))
  let β : (∀ w : S, (w.1.adicCompletion k)ˣ) →* Ideles k :=
    ∏ w : S, (localIdele k w.1).comp (Pi.evalMonoidHom (fun w : S => (w.1.adicCompletion k)ˣ) w)
  let γ : (∀ w : S, (w.1.adicCompletion k)ˣ) →* ℂˣ :=
    ∏ w : S, (θ w.1).comp (Pi.evalMonoidHom (fun w : S => (w.1.adicCompletion k)ˣ) w)
  have hβ : ∀ y, β y = ∏ w : S, localIdele k w.1 (y w) := fun y => MonoidHom.finsetProd_apply _ _ _
  have hγ : ∀ y, γ y = ∏ w : S, θ w.1 (y w) := fun y => MonoidHom.finsetProd_apply _ _ _
  have hβS : ∀ y (w : S), comp w.1 (β y) = y w := fun y w => by
    rw [hβ, map_prod, Finset.prod_eq_single w, comp_local_self]
    · exact fun w' _ h => comp_local_ne (fun e => h (Subtype.ext e.symm)) _
    · simp
  have hβn : ∀ y v, v ∉ S → comp v (β y) = 1 := fun y v hv => by
    rw [hβ, map_prod]
    exact Finset.prod_eq_one fun w _ => comp_local_ne (fun e : v = w.1 => hv (e ▸ w.2)) _
  obtain ⟨χ, hχ, -, hχU, hχα⟩ := GlobalTheory.exists_unitary_char_of_open_subgroup_and_hom (Ideles k)
    (kˣ × ∀ w : S, (w.1.adicCompletion k)ˣ) U hU ((diagUnits k).coprod β) ((1 : kˣ →* ℂˣ).coprod γ) 1 continuous_const
    (fun _ => by simp)
    (fun y => by
      have h1 : γ y.2 ^ m = 1 := by
        rw [hγ, ← Finset.prod_pow]
        exact Finset.prod_eq_one fun w _ => hm w w.2 _
      have h2 : ((γ y.2 : ℂˣ) : ℂ) ^ m = 1 := by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
      simpa using Complex.norm_eq_one_of_pow_eq_one h2 hm0.ne')
    (by
      rintro ⟨x, y⟩ ⟨h1, h2⟩
      have hval : ∀ (v : HeightOneSpectrum (𝓞 k)) (z : k),
          Valued.v (algebraMap k (v.adicCompletion k) z) = v.valuation k z := fun v z =>
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v z
      have hc : ∀ v, v ∉ S → GlobalTheory.LevelChars.compAt k v ((diagUnits k).coprod β (x, y)) =
          algebraMap k (v.adicCompletion k) (x : k) := fun v hv => by
        have e : comp v ((diagUnits k).coprod β (x, y)) = atFin v x := by
          rw [MonoidHom.coprod_apply, map_mul, comp_diag, hβn _ v hv, mul_one]
        exact congrArg Units.val e
      obtain ⟨z, hz⟩ := hT x (fun v hv => by rw [← hval, ← hc v hv]; exact (h1 v).1) (fun t ht => by
        have h3 := (h1 t).2 ht
        rw [hc t (Finset.disjoint_right.1 hST ht), ← map_one (algebraMap k (t.adicCompletion k)), ← map_sub, hval] at h3
        refine h3.trans_lt ?_
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
        simp)
      have hz0 : z ≠ 0 := by
        rintro rfl
        exact x.ne_zero (by rw [← hz, zero_pow hm0.ne'])
      have hxz : x = Units.mk0 z hz0 ^ m := Units.ext (by simp [hz])
      rw [MonoidHom.coprod_apply, MonoidHom.one_apply, MonoidHom.one_apply, one_mul, hγ]
      refine Finset.prod_eq_one fun w _ => ?_
      have h4 : θ w.1 (comp w.1 ((diagUnits k).coprod β (x, y))) = 1 := Subgroup.mem_iInf.1 h2 w
      rwa [MonoidHom.coprod_apply, map_mul, comp_diag, hβS, map_mul, hxz, map_pow, map_pow, hm w w.2, one_mul] at h4)
  let η : HChar k := ⟨χ, hχ, fun x => by simpa using hχα (x, 1)⟩
  have hinf : ∀ u : InfinitePlace k, η.locInf u = 1 := fun u => by
    ext x
    refine congrArg Units.val (hχU (infIdele k u x) ⟨fun v => ⟨map_one _, fun _ => ?_⟩, Subgroup.mem_iInf.2 fun w => ?_⟩)
    · change Valued.v ((1 : v.adicCompletion k) - 1) ≤ _
      simp
    · rw [Subgroup.mem_comap, comp_inf]
      exact one_mem _
  refine ⟨η, GlobalTheory.Mem.FinOrder.finite_order_of_inf_eq_one k η fun x => ?_, hinf, fun w hw => ?_⟩
  · change χ (infDiag x) = 1
    rw [infDiag, MonoidHom.finsetProd_apply, map_prod]
    exact Finset.prod_eq_one fun u _ => DFunLike.congr_fun (hinf u) (atInf u x)
  · refine MonoidHom.ext fun x => ?_
    have h := hχα (1, Pi.mulSingle (⟨w, hw⟩ : S) x)
    rw [MonoidHom.coprod_apply, MonoidHom.coprod_apply, map_one, map_one, one_mul, one_mul] at h
    dsimp only at h
    rw [hβ, hγ, Finset.prod_eq_single (⟨w, hw⟩ : S), Finset.prod_eq_single (⟨w, hw⟩ : S), Pi.mulSingle_eq_same] at h
    · exact h
    · intro w' _ h'
      rw [Pi.mulSingle_eq_of_ne h', map_one]
    · simp
    · intro w' _ h'
      rw [Pi.mulSingle_eq_of_ne h', map_one]
    · simp

end Global

end GlobalTheory.DelEps.Twist

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKCoord

theorem semiBC_injective {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) [Module.Projective A M]
    (hf : Function.Injective f) : Function.Injective u := by
  refine (injective_iff_map_eq_zero u).2 fun x hx => ?_
  by_contra h0
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero A h0
  obtain ⟨w, hw, -⟩ := h B (f.toSemilinearMap.comp φ)
  have h1 := hw x
  rw [hx, map_zero] at h1
  exact hφ (hf (h1.symm.trans (map_zero f).symm))

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]

theorem ev_eis_ne_zero (ϖ : PiSys l e) : ϖ.ev a (eis l a e) ≠ 0 := fun h =>
  (ϖ.isUnit_inclW_ev_eis a).ne_zero (by rw [h, map_zero])

theorem ev_injective (ϖ : PiSys l e) : Function.Injective (ϖ.ev a) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  have key : ∀ n : ℕ, ∃ y, x = eis l a e ^ n * y ∧ ϖ.ev a y = 0 := fun n => by
    induction n with
    | zero => exact ⟨x, by simp, hx⟩
    | succ n ih =>
      obtain ⟨y, h1, h2⟩ := ih
      obtain ⟨z, rfl⟩ := (ϖ.theta_ev_eq_zero_iff a y).1 (by rw [h2, map_zero])
      rw [map_mul] at h2
      exact ⟨z, by rw [h1]; ring, (mul_eq_zero.1 h2).resolve_left (ev_eis_ne_zero ϖ)⟩
  refine (complete_eis l a e).haus x fun n => ?_
  obtain ⟨y, h1, -⟩ := key n
  rw [SModEq.zero, h1]
  exact Submodule.smul_mem_smul
    (Ideal.pow_mem_pow (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) n) Submodule.mem_top

section Kappa

variable {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [Algebra O K] [NormedAlgebra ℚ_[l] K]
  {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O)

theorem kappa_smul (w : WCb l) :
    letI := zlLat T
    ∀ y : WCb l ⊗[ℤ_[l]] ↥T.L.T, kappa T (w • y) = ((1 : O) ⊗ₜ[ℤ_[l]] w : OW l O) • kappa T y := by
  letI := zlLat T
  intro y
  induction y using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul v x =>
    rw [smul_tmul', kappa_tmul, kappa_tmul, smul_tmul', smul_eq_mul, smul_eq_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), smul_add, hx, hy]

theorem kappa_frob :
    letI := zlLat T
    ∀ y : WCb l ⊗[ℤ_[l]] ↥T.L.T, kappa T (TensorProduct.map (frobW l).toLinearMap LinearMap.id y) =
      TWmap (frobOW l O) T (kappa T y) := by
  letI := zlLat T
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

def mulZ (o : O) :
    letI := zlLat T
    ↥T.L.T →ₗ[ℤ_[l]] ↥T.L.T :=
  letI := zlLat T
  { toFun := fun x => o • x
    map_add' := smul_add o
    map_smul' := fun c x => smul_comm o (algebraMap ℤ_[l] O c) x }

theorem kappa_mulZ (o : O) :
    letI := zlLat T
    ∀ y : WCb l ⊗[ℤ_[l]] ↥T.L.T, kappa T ((mulZ T o).lTensor (WCb l) y) = o • kappa T y := by
  letI := zlLat T
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | tmul v x => exact tmul_smul o ((1 : O) ⊗ₜ[ℤ_[l]] v : OW l O) x
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]

end Kappa

variable {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e} {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : Type} [Group G] [TopologicalSpace G] {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O}

theorem exists_coord (I : Ident t ϖ P T) {N : Type} [AddCommGroup N] (J : N →+ TW (OW l O) T)
    (h : ∀ y : TW (OW l O) T, (∃ x, y = J x) ↔
      ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) :
    ∃ (c : N →+ Vec K a ι) (hc : ∀ x, c x ∈ P.M),
      (∀ x, J x = I.j (toW t ϖ P ⟨c x, mem_ME_of_mem_M (hc x)⟩)) ∧ ∀ m ∈ P.M, ∃ x, c x = m := by
  choose c hc hJ using fun x => (h (J x)).1 ⟨x, rfl⟩
  refine ⟨AddMonoidHom.mk' c fun x y => ?_, hc, hJ, fun m hm => ?_⟩
  · have h1 := map_add J x y
    rw [hJ, hJ, hJ, ← map_add (f := _), ← map_add (f := _)] at h1
    exact congrArg Subtype.val (toW_injective t ϖ P (I.j.injective h1))
  · obtain ⟨x, hx⟩ := (h _).2 ⟨m, hm, rfl⟩
    rw [hJ] at hx
    exact ⟨x, (congrArg Subtype.val (toW_injective t ϖ P (I.j.injective hx))).symm⟩

theorem eq_of_j_eq (I : Ident t ϖ P T) (f : ZMod a → A O K) (v w : ME P)
    (h : I.j (toW t ϖ P w) = inclO l O (ϖ.iTot t K f) • I.j (toW t ϖ P v)) :
    w.1 = fun τ i => (f τ : K⟦X⟧) * v.1 τ i := by
  have hm : (fun τ i => (f τ : K⟦X⟧) * v.1 τ i) ∈ ME P :=
    mem_tot.2 fun τ i => mul_mem (le_away _ _ (f τ).2) (mem_tot.1 v.2 τ i)
  have h1 := toW_smul t ϖ P (fun τ => ⟨f τ, le_away _ _ (f τ).2⟩) v ⟨_, hm⟩ fun τ => rfl
  rw [← map_smul, ← ϖ.iW_of_mem t K, ← h1] at h
  exact congrArg Subtype.val (toW_injective t ϖ P (I.j.injective h))


variable (K t ϖ) in
theorem inclO_iTot_E_pow (k : ℕ) : inclO l O (ϖ.iTot t K ((fun _ => EIn l e _) ^ k)) =
    (1 : O) ⊗ₜ[ℤ_[l]] (inclW l (ϖ.ev a (eis l a e)) ^ k) := by
  rw [map_pow, map_pow, PiSys.iTot_E, inclO_tmul, Algebra.TensorProduct.tmul_pow, one_pow]

theorem eq_of_j_eq_const (I : Ident t ϖ P T) (o : O) (v w : ME P)
    (h : I.j (toW t ϖ P w) = o • I.j (toW t ϖ P v)) :
    w.1 = fun τ i => PowerSeries.C (algebraMap O K o) * v.1 τ i := by
  refine (eq_of_j_eq I (algebraMap O _ o) v w ?_).trans
    (funext fun τ => funext fun i => congrArg (· * v.1 τ i) (algebraMap_eq_C o))
  rwa [AlgHom.commutes, AlgHom.commutes, algebraMap_smul]

theorem eq_of_j_eq_toAc (I : Ident t ϖ P T) (f : (Wq l a)⟦X⟧) (v w : ME P)
    (h : I.j (toW t ϖ P w) = ((1 : O) ⊗ₜ[ℤ_[l]] inclW l (ϖ.ev a f) : OW l O) • I.j (toW t ϖ P v)) :
    w.1 = fun τ i => (toAc t K f τ : K⟦X⟧) * v.1 τ i := by
  refine eq_of_j_eq I (toAc t K f) v w ?_
  rwa [PiSys.iTot_toAc, inclO_tmul]

theorem eq_of_j_eq_phi (I : Ident t ϖ P T) (k : ℕ) {v : Vec K a ι} (hv : v ∈ P.M) (w : ME P)
    (h : I.j (toW t ϖ P w) = ((1 : O) ⊗ₜ[ℤ_[l]] (inclW l (ϖ.ev a (eis l a e)) ^ k) : OW l O) •
      TWmap (frobOW l O) T (I.j (toW t ϖ P ⟨v, mem_ME_of_mem_M hv⟩))) :
    w.1 = fun τ i => E K l e ^ k * P.phi v τ i := by
  refine eq_of_j_eq I ((fun _ => EIn l e _) ^ k) ⟨_, mem_ME_of_mem_L (P.phi_mem_L hv)⟩ w ?_
  rwa [toW_phi t ϖ P hv, I.j_φ, inclO_iTot_E_pow]

theorem j_frob {EE : FCrys l ↥(OL (ϖ.field a))} {T : Type} [AddCommGroup T] [Module ℤ_[l] T]
    {ρ : ↥(GK (ϖ.field a)) → (T →ₗ[ℤ_[l]] T)}
    {j : EE.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] T)}
    (H : Realises (ϖ.field a) EE (ainfObj _) (ainfId _) T ρ j) (x m : EE.M (ϖ.prism a)) (k : ℕ)
    (h : IsFrac (A := (ϖ.prism a).A) (eis l a e)
      (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ x) m k) :
    j (EE.tr (ϖ.toAinf a) m) = inclW l (ϖ.ev a (eis l a e)) ^ k •
      TensorProduct.map (frobW l).toLinearMap LinearMap.id (j (EE.tr (ϖ.toAinf a) x)) := by
  let d : ↥(ainfObj (ϖ.field a)).I := ⟨ϖ.ev a (eis l a e), ϖ.theta_ev_eis a⟩
  obtain ⟨n, i, hn⟩ := exists_isFrac (d : (ainfObj (ϖ.field a)).A) (EE.Φ _ d (EE.tr (ϖ.toAinf a) x))
  obtain ⟨r, hr⟩ := EE.Φ_nat (ϖ.toAinf a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ d x m k n i h hn
  have h1 := H.j_φ d (ev_eis_ne_zero ϖ) _ n i hn
  have : IsDomain (ainfObj (ϖ.field a)).A := (ainfId (ϖ.field a)).toMulEquiv.isDomain
  have := EE.proj (ainfObj (ϖ.field a))
  have h0 : (d : (ainfObj (ϖ.field a)).A) ≠ 0 := ev_eis_ne_zero ϖ
  have h2 : (d : (ainfObj (ϖ.field a)).A) ^ i • EE.tr (ϖ.toAinf a) m = (d : (ainfObj (ϖ.field a)).A) ^ k • n :=
    sub_eq_zero.1 ((smul_eq_zero.1 hr).resolve_left (pow_ne_zero _ (mul_ne_zero h0 h0)))
  exact (smul_eq_of_isUnit j (ϖ.isUnit_inclW_ev_eis a) h2 h1).symm

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : GlobalTheory.BKReal.Lat a O K ϖ) (I : Ident t ϖ P T), GlobalTheory.Published.BhattScholzeCrystallineLattices → IsBK I → ∃ (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), Function.Injective c ∧ (∀ x, c x ∈ P.M) ∧ (∀ m ∈ P.M, ∃ x, c x = m) ∧ (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) ∧ (∀ o : O, ∃ U : FHom EE EE, ∀ x, c (U.u (ϖ.prism a) x) = fun τ i => PowerSeries.C (algebraMap O K o) * c x τ i) ∧ (∀ (x m : EE.M (ϖ.prism a)) (k : ℕ), IsFrac (A := (ϖ.prism a).A) (eis l a e) (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ x) m k → c m = fun τ i => E K l e ^ k * P.phi (c x) τ i) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I hBS hBK
  letI := zlLat T
  obtain ⟨EE, j, H, him⟩ := hBK
  have h0 : ∃ J : EE.M (ϖ.prism a) →+ TW (OW l O) T, ∀ x, J x = kappa T (j (EE.tr (ϖ.toAinf a) x)) :=
    ⟨(kappa T).comp (j.toAddMonoidHom.comp (EE.tr (ϖ.toAinf a)).toAddMonoidHom), fun _ => rfl⟩
  obtain ⟨J, hJ⟩ := h0
  have h1 : ∀ y : TW (OW l O) T, (∃ x, y = J x) ↔
      ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩) := fun y => by
    simp only [hJ]
    exact him y
  have h2 := exists_coord I J h1
  obtain ⟨c, hc, hcJ, hs⟩ := h2
  have hi : Function.Injective J := by
    have := EE.proj (ainfObj (ϖ.field a))
    have := EE.proj (ϖ.prism a)
    intro x y h
    rw [hJ, hJ] at h
    exact semiBC_injective (EE.tr_bc (ϖ.toAinf a)) (ev_injective ϖ)
      (semiBC_injective H.bc inclW_injective ((kappa_bijective T).1 h))
  refine ⟨EE, c, fun x y hxy => hi ?_, hc, hs, fun w x => ?_, fun o => ?_, fun x m k h => ?_⟩
  · rw [hcJ, hcJ]
    simp only [hxy]
  · refine eq_of_j_eq_toAc I w ⟨_, mem_ME_of_mem_M (hc x)⟩ ⟨_, mem_ME_of_mem_M (hc _)⟩ ?_
    have h3 := congrArg j ((EE.tr (ϖ.toAinf a)).map_smulₛₗ w x)
    have h4 := congrArg (kappa T) (h3.trans (j.map_smulₛₗ _ _))
    have h5 := h4.trans (kappa_smul T _ _)
    rewrite [← hcJ, ← hcJ, hJ, hJ]
    exact h5
  · have h3 := (hBS l _ _ _ (isAinf_ainfObj (ϖ.field a))).2 _ _ _ _ EE EE j j H H (mulZ T o)
      fun g x => ((T.actT g).map_smul o x).symm
    obtain ⟨U, hU, -⟩ := h3
    refine ⟨U, fun x => eq_of_j_eq_const I o ⟨_, mem_ME_of_mem_M (hc x)⟩ ⟨_, mem_ME_of_mem_M (hc _)⟩ ?_⟩
    have h3 := (congrArg j (U.u_tr (ϖ.toAinf a) x)).symm.trans (hU _)
    have h4 := (congrArg (kappa T) h3).trans (kappa_mulZ T o _)
    rewrite [← hcJ, ← hcJ, hJ, hJ]
    exact h4
  · refine eq_of_j_eq_phi I k (hc x) ⟨_, mem_ME_of_mem_M (hc _)⟩ ?_
    have h3 := (congrArg (kappa T) (j_frob H x m k h)).trans (kappa_smul T _ _)
    have h4 := kappa_frob T (j (EE.tr (ϖ.toAinf a) x))
    rewrite [← hcJ, ← hcJ, hJ, hJ, ← h4]
    exact h3

end GlobalTheory.BKCoord
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.tensor_fundamental_exact_sequence_crystalline : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V], (∀ (u : V ⊗[ℚ_[l]] P.R.B) (w : V ⊗[ℚ_[l]] P.R.BdR), ∃ (x : V ⊗[ℚ_[l]] P.R.B) (y : V ⊗[ℚ_[l]] P.R.BdR), y ∈ FilV (P.PD K) (LL := LL) (V := V) 0 ∧ x - φVB (P.PD K) (LL := LL) (V := V) x = u ∧ ιV (P.PD K) (LL := LL) (V := V) x - y = w) ∧ ∀ x : V ⊗[ℚ_[l]] P.R.B, φVB (P.PD K) (LL := LL) (V := V) x = x → ιV (P.PD K) (LL := LL) (V := V) x ∈ FilV (P.PD K) (LL := LL) (V := V) 0 → ∃ v : V, x = v ⊗ₜ[ℚ_[l]] (1 : P.R.B) := by
  first | exact @GlobalTheory.FundSeq.tensor_fundamental_sequence | exact GlobalTheory.FundSeq.tensor_fundamental_sequence | (intros; apply GlobalTheory.FundSeq.tensor_fundamental_sequence <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt


theorem _root_.GlobalTheory.T.card_eq_of_linIndep_spanning_deRham : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (a m : ℕ) (w : Fin m → Fin a → P.R.BdR), (∀ β : Fin m → P.R.BdR, ∑ i, β i • w i = 0 → β = 0) → (∀ j, ∃ u : Fin m → P.R.BdR, ∑ i, u i • w i = Pi.single j 1) → m = a := by
  first | exact @GlobalTheory.card_eq_of_indep_spans_dR | exact GlobalTheory.card_eq_of_indep_spans_dR | (intros; apply GlobalTheory.card_eq_of_indep_spans_dR <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.dcris_span_tensorBcris_rat : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsCrys (P.PD K) ρ → ∀ y : V ⊗[ℚ_[l]] P.R.B, ∃ (m : ℕ) (b : Fin m → P.R.B) (d : Fin m → V ⊗[ℚ_[l]] P.R.B), (∀ i, d i ∈ Dcris (P.PD K) ρ) ∧ y = ∑ i, AlgebraTensorModule.map (LinearMap.id : V →ₗ[ℚ_[l]] V) (LinearMap.mulLeft ℚ_[l] (b i)) (d i) := by
  first | exact @GlobalTheory.Per.RatSpan.crisSpan_rat | exact GlobalTheory.Per.RatSpan.crisSpan_rat | (intros; apply GlobalTheory.Per.RatSpan.crisSpan_rat <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

theorem _root_.GlobalTheory.T.wachLattice_expansions_std_below_level : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1), ζ ^ (l ^ (s - 1)) = 1 → Std (Di (HW l) h T i) (Lat C h T i ζ) := by
  first | exact @GlobalTheory.NL.LatLow.lat_low | exact GlobalTheory.NL.LatLow.lat_low | (intros; apply GlobalTheory.NL.LatLow.lat_low <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.etaleFunctor_exact_on_lattices : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsSESLat (Qp := ℚ_[l]) (O := ↥(OL LL)) ι π → Function.Injective (W.map ι) ∧ Function.Surjective (W.map π) ∧ ∀ x, W.map π x = 0 ↔ ∃ y, W.map ι y = x := by
  first | exact @GlobalTheory.LatExact.W_exact | exact GlobalTheory.LatExact.W_exact | (intros; apply GlobalTheory.LatExact.W_exact <;> assumption)
end
