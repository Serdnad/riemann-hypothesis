module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalDomainPrime
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1735
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1733
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1657
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle759
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle761
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle825
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle598
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle762
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1737
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section

namespace GlobalTheory.Div.FramePull

variable {X X₀ : Scheme.{0}}

theorem isUnit_res_of_le {V U : X₀.Opens} (f : Γ(X₀, U)) (h : V ≤ X₀.basicOpen f) :
    IsUnit ((X₀.presheaf.map (homOfLE (h.trans (X₀.basicOpen_le f))).op).hom f) := by
  have e : (X₀.presheaf.map (homOfLE (h.trans (X₀.basicOpen_le f))).op).hom f =
      (X₀.presheaf.map (homOfLE h).op).hom ((X₀.presheaf.map (homOfLE (X₀.basicOpen_le f)).op).hom f) := by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
  rw [e]
  exact (X₀.toRingedSpace.isUnit_res_basicOpen f).map _

theorem le_basicOpen {H : LB X₀} (s : LB.Sec H) (a : H.ι) :
    nonzeroLocus s ⊓ H.U a ≤ X₀.basicOpen (s.f a) := by
  rintro z ⟨hz, ha⟩
  obtain ⟨a', ha'⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  have e := congrArg X₀.basicOpen (s.compat a a')
  rw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (H.g a a').isUnit, Scheme.basicOpen_res,
    Scheme.basicOpen_res] at e
  have hm : z ∈ H.U a ⊓ H.U a' ⊓ X₀.basicOpen (s.f a) := by
    rw [e]; exact ⟨⟨ha, X₀.basicOpen_le _ ha'⟩, ⟨ha, X₀.basicOpen_le _ ha'⟩, ha'⟩
  exact hm.2

theorem gm_gen_div {M L' : LB X₀} {w : LB.Iso L' M} (hw : w.IsGen) (z : X₀) (p q : M.ι × L'.ι)
    (hp : z ∈ M.U p.1 ⊓ L'.U p.2) (hq : z ∈ M.U q.1 ⊓ L'.U q.2) :
    gm (𝟙 X₀) z _ (w.s p) = gm (𝟙 X₀) z (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1) *
      (gm (𝟙 X₀) z (L'.U p.2 ⊓ L'.U q.2) (L'.g p.2 q.2))⁻¹ * gm (𝟙 X₀) z _ (w.s q) := by
  have hm : z ∈ (LB.div M L').U p ⊓ (LB.div M L').U q := ⟨hp, hq⟩
  have := congrArg (gm (𝟙 X₀) z _) (hw p q)
  rw [gm_res _ z _ hm, map_mul, gm_res _ z _ hm] at this
  rw [this]
  refine congrArg (· * _) ?_
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ z _ hm _)
    ((map_inv _ _).trans (congrArg _ (gm_res _ z _ hm _))))

theorem gm_pull_g (L : LB X) (γ : X₀ ⟶ X) (z : X₀) (m m' : L.ι) (hm : γ z ∈ L.U m) (hm' : γ z ∈ L.U m') :
    gm (𝟙 X₀) z ((L.pull γ).U (fun _ => m) ⊓ (L.pull γ).U (fun _ => m'))
      ((L.pull γ).g (fun _ => m) (fun _ => m')) = gm γ z _ (L.g m m') := by
  have hp : z ∈ (L.pull γ).U (fun _ => m) ⊓ (L.pull γ).U (fun _ => m') := ⟨mem_pull.2 hm, mem_pull.2 hm'⟩
  show gm (𝟙 X₀) z _ (∏ _k : PUnit, (res _ (pullU γ _ (L.g m m'))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  refine (gm_res _ z _ hp _).trans ((gm_pull (𝟙 X₀) γ z (L.U m ⊓ L.U m') ⟨hm, hm'⟩ _).trans ?_)
  rw [Category.id_comp]

theorem grp₁ {M : Type} [CommGroup M] (G S W : M) (k : ℕ) :
    (G * S) ^ k * (G ^ (k : ℤ) * 1⁻¹ * W)⁻¹ = S ^ k * W⁻¹ := by
  rw [zpow_natCast, inv_one, mul_one, mul_pow, mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]

theorem grp₂ {M : Type} [CommGroup M] (S Γ W : M) (k : ℕ) :
    S ^ k * ((1 : M) ^ (k : ℤ) * Γ⁻¹ * W)⁻¹ = Γ * (S ^ k * W⁻¹) := by
  rw [one_zpow, one_mul, mul_inv, inv_inv, mul_left_comm]

theorem frame_pull : ∀ (X X₀ : Scheme.{0}) (γ : X₀ ⟶ X) (H₀ : LB X₀) (s : LB.Sec H₀) (k : ℕ) (L : LB X), L.IsLB →
    H₀.IsLB → ∀ (w : LB.Iso (L.pull γ) (pw H₀ k)), w.IsGen → ∀ (D : X.Opens), γ ⁻¹ᵁ D = nonzeroLocus s →
    ∃ u : ∀ m : L.ι, Γ(X₀, γ ⁻¹ᵁ (D ⊓ L.U m))ˣ, (∀ z m m', γ z ∈ D ⊓ L.U m → γ z ∈ D ⊓ L.U m' →
      gm (𝟙 X₀) z _ (u m) = gm γ z _ (L.g m m') * gm (𝟙 X₀) z _ (u m')) ∧
      ∀ z m a, γ z ∈ D ⊓ L.U m → z ∈ H₀.U a →
        gs (𝟙 X₀) z _ (s.f a) ^ k = (gm (𝟙 X₀) z _ (u m)).val * (gm (𝟙 X₀) z _ (w.s (a, fun _ => m))).val := by
  intro X X₀ γ H₀ s k L hL hH w hw D hD
  let W : L.ι → H₀.ι → X₀.Opens := fun m a => γ ⁻¹ᵁ (D ⊓ L.U m) ⊓ H₀.U a
  have hWb : ∀ m a, W m a ≤ X₀.basicOpen (s.f a) := fun m a z hz =>
    le_basicOpen s a ⟨hD ▸ (show z ∈ γ ⁻¹ᵁ D from hz.1.1), hz.2⟩
  have hWw : ∀ m a, W m a ≤ (LB.div (pw H₀ k) (L.pull γ)).U (a, fun _ => m) := fun m a z hz =>
    ⟨hz.2, mem_pull.2 hz.1.2⟩
  let S : ∀ m a, Γ(X₀, W m a)ˣ := fun m a => (isUnit_res_of_le (s.f a) (hWb m a)).unit
  let v : ∀ m a, Γ(X₀, W m a)ˣ := fun m a => S m a ^ k * (res (hWw m a) (w.s (a, fun _ => m)))⁻¹
  have hS : ∀ m a z (hz : z ∈ W m a), (gm (𝟙 X₀) z _ (S m a)).val = gs (𝟙 X₀) z _ (s.f a) := by
    intro m a z hz
    rw [← gs_unit _ z _ hz, IsUnit.unit_spec]
    exact gs_res _ z _ hz _
  have hv : ∀ m a z (hz : z ∈ W m a), gm (𝟙 X₀) z _ (v m a) =
      gm (𝟙 X₀) z _ (S m a) ^ k * (gm (𝟙 X₀) z _ (w.s (a, fun _ => m)))⁻¹ := by
    intro m a z hz
    simp only [v, map_mul, map_pow, map_inv]
    rw [gm_res _ z _ hz]

  have hwg : ∀ z a a' m m', z ∈ H₀.U a → z ∈ H₀.U a' → γ z ∈ L.U m → γ z ∈ L.U m' →
      gm (𝟙 X₀) z _ (w.s (a, fun _ => m)) = gm (𝟙 X₀) z (H₀.U a ⊓ H₀.U a') (H₀.g a a') ^ (k : ℤ) *
        (gm γ z _ (L.g m m'))⁻¹ * gm (𝟙 X₀) z _ (w.s (a', fun _ => m')) := by
    intro z a a' m m' ha ha' hm hm'
    rw [gm_gen_div hw z (a, fun _ => m) (a', fun _ => m') ⟨ha, mem_pull.2 hm⟩ ⟨ha', mem_pull.2 hm'⟩,
      gm_pull_g L γ z m m' hm hm']
    exact congrArg (fun t => t * _ * _) (map_zpow _ _ _)
  have hSg : ∀ m m' a a' z (hz : z ∈ W m a) (hz' : z ∈ W m' a'),
      gm (𝟙 X₀) z _ (S m a) = gm (𝟙 X₀) z (H₀.U a ⊓ H₀.U a') (H₀.g a a') * gm (𝟙 X₀) z _ (S m' a') := by
    intro m m' a a' z hz hz'
    apply Units.ext
    rw [Units.val_mul, hS m a z hz, hS m' a' z hz']
    exact gs_sec_chart s (𝟙 X₀) z hz.2 hz'.2
  have glue : ∀ m, ∃ t : Γ(X₀, γ ⁻¹ᵁ (D ⊓ L.U m))ˣ, ∀ a, res (inf_le_left : W m a ≤ _) t = v m a := by
    intro m
    refine glue_unit (γ ⁻¹ᵁ (D ⊓ L.U m)) (W m) (fun a => inf_le_left) (fun z hz => ?_) (v m) ?_
    · obtain ⟨a, ha⟩ := exists_chart hH z
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, hz, ha⟩
    · intro a a' z hz
      rw [hv m a z hz.1, hv m a' z hz.2, hSg m m a a' z hz.1 hz.2,
        hwg z a a' m m hz.1.2 hz.2.2 hz.1.1.2 hz.1.1.2, gm_self hL γ z hz.1.1.2]
      exact grp₁ _ _ _ k
  choose u hu using glue
  have hug : ∀ m a z (hz : z ∈ W m a), gm (𝟙 X₀) z _ (u m) = gm (𝟙 X₀) z _ (v m a) := by
    intro m a z hz
    rw [← hu m a, gm_res _ z _ hz]
  refine ⟨u, fun z m m' hm hm' => ?_, fun z m a hm ha => ?_⟩
  · obtain ⟨a, ha⟩ := exists_chart hH z
    have hz : z ∈ W m a := ⟨hm, ha⟩
    have hz' : z ∈ W m' a := ⟨hm', ha⟩
    rw [hug m a z hz, hug m' a z hz', hv m a z hz, hv m' a z hz', hSg m m' a a z hz hz',
      gm_self hH (𝟙 X₀) z ha, one_mul, hwg z a a m m' ha ha hm.2 hm'.2, gm_self hH (𝟙 X₀) z ha]
    exact grp₂ _ _ _ k
  · have hz : z ∈ W m a := ⟨hm, ha⟩
    rw [hug m a z hz, hv m a z hz, ← hS m a z hz, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_mul_cancel_right]

end GlobalTheory.Div.FramePull
end
end

section

open GlobalTheory.LN

namespace GlobalTheory.ValCrit


open Polynomial in
theorem _root_.GlobalTheory.ValCrit.isIntegral_of_mem_adjoin_inv {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (y : K) (hy : y ≠ 0)
    (h : y⁻¹ ∈ Algebra.adjoin R {y}) : IsIntegral R y⁻¹ := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at h
  obtain ⟨p, hp⟩ := h
  letI : Invertible y := invertibleOfNonzero hy
  set n := p.natDegree
  have hrefl : (reflect n p).degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt (degree_le_natDegree) ?_
    have : (reflect n p).natDegree ≤ n := natDegree_reflect_le.trans (by simp [n])
    exact_mod_cast Nat.lt_succ_of_le this
  refine ⟨X ^ (n + 1) - reflect n p, monic_X_pow_sub hrefl, ?_⟩
  have key := eval₂_reflect_mul_pow (algebraMap R K) y n p le_rfl
  rw [invOf_eq_inv] at key
  have hp' : eval₂ (algebraMap R K) y p = y⁻¹ := hp
  rw [hp'] at key
  have hval : eval₂ (algebraMap R K) y⁻¹ (reflect n p) = y⁻¹ ^ (n + 1) := by
    have hyn : y ^ n ≠ 0 := pow_ne_zero _ hy
    rw [← mul_inv_cancel_right₀ hyn (eval₂ (algebraMap R K) y⁻¹ (reflect n p)), key, pow_succ,
      inv_pow, mul_comm]
  rw [eval₂_sub, eval₂_X_pow, hval, sub_self]

private theorem maximalIdeal_map_sup_span_ne_univ_of_inv_not_mem_adjoin {R K : Type} [CommRing R]
    [IsLocalRing R] [Field K] [Algebra R K] (y : K) (hnot : y⁻¹ ∉ Algebra.adjoin R {y}) :
    (IsLocalRing.maximalIdeal R).map (algebraMap R (Algebra.adjoin R {y})) ⊔
      Ideal.span {(⟨y, Algebra.self_mem_adjoin_singleton R y⟩ : Algebra.adjoin R {y})} ≠ ⊤ := by
  set S := Algebra.adjoin R {y}
  set ys : S := ⟨y, Algebra.self_mem_adjoin_singleton R y⟩
  intro hJ
  set π := Ideal.Quotient.mk (Ideal.span {ys})
  have hsurj : Function.Surjective (π.comp (algebraMap R S)) := by
    intro s
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective s
    have hs2 : (s : K) ∈ (Polynomial.aeval (R := R) y).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]
      exact s.2
    obtain ⟨f, hf⟩ := hs2
    have hfs : Polynomial.aeval ys f = s :=
      Subtype.ext (by rw [← hf, Polynomial.aeval_subalgebra_coe]; rfl)
    refine ⟨f.coeff 0, ?_⟩
    rw [← hs, ← hfs, RingHom.comp_apply]
    conv_rhs => rw [← Polynomial.X_mul_divX_add f]
    rw [map_add (f := _), map_mul, Polynomial.aeval_X, Polynomial.aeval_C, map_add (f := _), map_mul,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self ys), zero_mul, zero_add]
  have htop : (IsLocalRing.maximalIdeal R).map (π.comp (algebraMap R S)) = ⊤ := by
    have := congrArg (Ideal.map π) hJ
    rwa [Ideal.map_sup, Ideal.map_map, Ideal.map_quotient_self, sup_bot_eq, Ideal.map_top] at this
  obtain ⟨a, ha, ha1⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).1
    (htop ▸ Submodule.mem_top : (1 : S ⧸ Ideal.span {ys}) ∈ _)
  have hmem : ys ∣ algebraMap R S (1 - a) := by
    rw [← Ideal.mem_span_singleton, map_sub, map_one, ← Ideal.Quotient.eq]
    exact ha1.symm
  have hunitA : IsUnit (algebraMap R S (1 - a)) :=
    (IsLocalRing.isUnit_one_sub_self_of_mem_nonunits a
      ((IsLocalRing.mem_maximalIdeal a).1 ha)).map _
  obtain ⟨u, hu⟩ := isUnit_of_dvd_unit hmem hunitA
  apply hnot
  have h1 : ((u⁻¹ : Sˣ) : S) * ys = 1 := by rw [← hu, Units.inv_mul]
  have h2 : (((u⁻¹ : Sˣ) : S) : K) = y⁻¹ := eq_inv_of_mul_eq_one_left (congrArg Subtype.val h1)
  exact h2 ▸ ((u⁻¹ : Sˣ) : S).2

theorem _root_.GlobalTheory.ValCrit.dvd_of_forall_cdvr : ∀ (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (p q : R), q ≠ 0 →
    (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V),
      _root_.GlobalTheory.LN.CDvr V → Function.Injective φ →
      (IsLocalRing.maximalIdeal V).comap φ = IsLocalRing.maximalIdeal R → φ q ∣ φ p) →
    q ∣ p := by
  intro R _ _ _ _ _ _ p q hq H
  by_cases hp : p = 0
  · exact hp ▸ dvd_zero q
  by_contra hdvd
  set K := FractionRing R
  have hinjK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hpK : algebraMap R K p ≠ 0 := (map_ne_zero_iff _ hinjK).2 hp
  have hqK : algebraMap R K q ≠ 0 := (map_ne_zero_iff _ hinjK).2 hq
  set y : K := algebraMap R K q / algebraMap R K p with hy_def
  have hy : y ≠ 0 := div_ne_zero hqK hpK
  set S := Algebra.adjoin R {y}
  have hnot : y⁻¹ ∉ S := by
    intro hmem
    have hint := _root_.GlobalTheory.ValCrit.isIntegral_of_mem_adjoin_inv y hy hmem
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine hdvd ⟨r, hinjK ?_⟩
    rw [map_mul, hr, hy_def, inv_div, mul_comm, div_mul_cancel₀ _ hqK]
  let ys : S := ⟨y, Algebra.self_mem_adjoin_singleton R y⟩
  have hinjS : Function.Injective (algebraMap R S) := by
    intro a b hab
    exact hinjK (congrArg Subtype.val hab)
  haveI : Algebra.FiniteType R S := Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton y)
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  haveI : CharZero S := charZero_of_injective_algebraMap hinjS
  set J : Ideal S := (IsLocalRing.maximalIdeal R).map (algebraMap R S) ⊔ Ideal.span {ys}
  have hJ : J ≠ ⊤ := maximalIdeal_map_sup_span_ne_univ_of_inv_not_mem_adjoin y hnot
  obtain ⟨P, hPmax, hJP⟩ := Ideal.exists_le_maximal J hJ
  have hyP : ys ∈ P := hJP (Ideal.mem_sup_right (Ideal.mem_span_singleton_self ys))
  have hcomapP : P.comap (algebraMap R S) = IsLocalRing.maximalIdeal R := by
    refine ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le ?_ ?_).symm
    · exact (hPmax.isPrime.comap (algebraMap R S)).ne_top
    · exact Ideal.map_le_iff_le_comap.1 (le_trans le_sup_left hJP)
  obtain ⟨V, _, _, _, φ, hV, hφ, hcomap⟩ :=
    _root_.GlobalTheory.PrimeUnif.exists_cdvr S P
  have hψ : Function.Injective (φ.comp (algebraMap R S)) := hφ.comp hinjS
  have hψc : (IsLocalRing.maximalIdeal V).comap (φ.comp (algebraMap R S)) =
      IsLocalRing.maximalIdeal R := by
    rw [← Ideal.comap_comap, hcomap, hcomapP]
  obtain ⟨v, hv⟩ := H V (φ.comp (algebraMap R S)) hV hψ hψc
  have hrel : ys * algebraMap R S p = algebraMap R S q := by
    apply Subtype.ext
    change y * algebraMap R K p = algebraMap R K q
    rw [hy_def, div_mul_cancel₀ _ hpK]
  have hψp : φ (algebraMap R S p) ≠ 0 := by
    intro h0
    exact hp (hψ (by simpa using h0))
  have hone : φ ys * v = 1 := by
    apply mul_left_cancel₀ hψp
    simp only [RingHom.comp_apply] at hv
    rw [← hrel, map_mul] at hv
    calc φ (algebraMap R S p) * (φ ys * v) = φ ys * φ (algebraMap R S p) * v := by ring
      _ = φ (algebraMap R S p) := hv.symm
      _ = φ (algebraMap R S p) * 1 := (mul_one _).symm
  have hunit : IsUnit (φ ys) := isUnit_iff_exists_inv.2 ⟨v, hone⟩
  have hys : ys ∉ P := by
    rw [← hcomap, Ideal.mem_comap]
    exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h hunit
  exact hys hyP

end GlobalTheory.ValCrit
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem lid_baseChange_self {K M N : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N]
    [Module K N] (f : M →ₗ[K] N) (x : K ⊗[K] M) :
    TensorProduct.lid K N (f.baseChange K x) = f (TensorProduct.lid K M x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem nonempty_equiv_homology_of_baseChange_self {K : Type} [Field K]
    (S : ShortComplex (ModuleCat.{0} K)) {H : Type} [AddCommGroup H] [Module K H]
    (θ : LinearMap.ker (S.g.hom.baseChange K) →ₗ[K] H) (hs : Function.Surjective θ)
    (hk : ∀ z, θ z = 0 ↔ z.1 ∈ LinearMap.range (S.f.hom.baseChange K)) :
    Nonempty (H ≃ₗ[K] S.homology) := by
  have hmem : ∀ x : LinearMap.ker S.g.hom,
      (TensorProduct.lid K S.X₂).symm x.1 ∈ LinearMap.ker (S.g.hom.baseChange K) := by
    intro x
    rw [LinearMap.mem_ker]
    apply (TensorProduct.lid K S.X₃).injective
    rw [lid_baseChange_self, LinearEquiv.apply_symm_apply, map_zero]
    exact x.2
  let q : LinearMap.ker S.g.hom →ₗ[K] H :=
    θ ∘ₗ ((((TensorProduct.lid K S.X₂).symm : S.X₂ →ₗ[K] K ⊗[K] S.X₂) ∘ₗ
      (LinearMap.ker S.g.hom).subtype).codRestrict _ hmem)
  have hq : ∀ x, q x = θ ⟨(TensorProduct.lid K S.X₂).symm x.1, hmem x⟩ := fun x => rfl
  have hsurj : Function.Surjective q := by
    intro h
    obtain ⟨z, rfl⟩ := hs h
    have hz : TensorProduct.lid K S.X₂ z.1 ∈ LinearMap.ker S.g.hom := by
      rw [LinearMap.mem_ker, ← lid_baseChange_self, z.2, map_zero]
    refine ⟨⟨_, hz⟩, ?_⟩
    rw [hq]
    congr 1
    exact Subtype.ext (LinearEquiv.symm_apply_apply _ _)
  have hker : LinearMap.range S.moduleCatToCycles = LinearMap.ker q := by
    ext x
    rw [LinearMap.mem_ker, hq, hk]
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨(TensorProduct.lid K S.X₁).symm y, ?_⟩
      apply (TensorProduct.lid K S.X₂).injective
      rw [lid_baseChange_self, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      rfl
    · rintro ⟨y, hy⟩
      refine ⟨TensorProduct.lid K S.X₁ y, Subtype.ext ?_⟩
      have := congrArg (TensorProduct.lid K S.X₂) hy
      rw [lid_baseChange_self, LinearEquiv.apply_symm_apply] at this
      exact this
  exact ⟨((q.quotKerEquivOfSurjective hsurj).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hker.symm ≪≫ₗ
    S.moduleCatHomologyIso.toLinearEquiv.symm)⟩

theorem hO_equiv_cech : ∀ (K : Type) [Field K] (X : Scheme.{0}) (s : X ⟶ Sp K) (κ : Type) [LinearOrder κ]
    [Fintype κ] (D : κ → X.Opens), IsSeparated s → (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ →
    Nonempty (HO1 s ≃ₗ[K] (cechLB s (LB.triv X) D).homology 1) ∧
      Nonempty (HO2 s ≃ₗ[K] (cechLB s (LB.triv X) D).homology 2) := by
  intro K _ X s κ _ _ D hsep haff hcov
  obtain ⟨M⟩ := GlobalTheory.T.orderedCech_finiteAffineCover_models_structureSheafCohomology K X s κ D hsep haff hcov
  have hsp : spMap (algebraMap K K) = 𝟙 (Sp K) := by
    rw [Algebra.algebraMap_self]; exact Spec.map_id _
  have hP : IsPullback (𝟙 X) s s (spMap (algebraMap K K)) := by
    rw [hsp]; exact IsPullback.id_horiz s
  obtain ⟨h1s, h1k, h2s, h2k⟩ := M.exact hP
  obtain ⟨e1⟩ := nonempty_equiv_homology_of_baseChange_self ((cechLB s (LB.triv X) D).sc' 0 1 2) (M.θ1 hP) h1s h1k
  obtain ⟨e2⟩ := nonempty_equiv_homology_of_baseChange_self ((cechLB s (LB.triv X) D).sc' 1 2 3) (M.θ2 hP) h2s h2k
  exact ⟨⟨e1 ≪≫ₗ ((cechLB s (LB.triv X) D).homologyIsoSc' 0 1 2 (by simp) (by simp)).toLinearEquiv.symm⟩,
    ⟨e2 ≪≫ₗ ((cechLB s (LB.triv X) D).homologyIsoSc' 1 2 3 (by simp) (by simp)).toLinearEquiv.symm⟩⟩

end GlobalTheory.AbCoh
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.AbCoh

theorem primF_of_abelian (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hs : SmoothOfRelativeDimension g A.hom) : PrimF A := by
  obtain ⟨-, -, hAA, hsAA⟩ := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hA hs
  have hax := (GlobalTheory.T.grpObj_pullback_axes_cohomology_projections R A).2.1
  have hM : FP R (GlobForm A.hom × GlobForm A.hom) (g + g) :=
    (GlobalTheory.T.fgProjectiveConstantRank_extension_and_prod).2 R _ _ g g (GlobalTheory.T.abelianScheme_global_oneForms_projective_rank R A g hA hs) (GlobalTheory.T.abelianScheme_global_oneForms_projective_rank R A g hA hs)
  have hN : FP R (GlobForm (A ⊗ A).hom) (g + g) := GlobalTheory.T.abelianScheme_global_oneForms_projective_rank R (A ⊗ A) (g + g) hAA hsAA
  let i₁ : A ⟶ A ⊗ A := lift (𝟙 A) (toUnit A ≫ η[A])
  let i₂ : A ⟶ A ⊗ A := lift (toUnit A ≫ η[A]) (𝟙 A)
  let f : (GlobForm A.hom × GlobForm A.hom) →ₗ[R] GlobForm (A ⊗ A).hom :=
    (pF (fst A A)).coprod (pF (snd A A))
  let r : GlobForm (A ⊗ A).hom →ₗ[R] (GlobForm A.hom × GlobForm A.hom) :=
    (pF i₁).prod (pF i₂)
  have hr : ∀ y, r y = (pF i₁ y, pF i₂ y) := fun y ↦ by simp [r, LinearMap.prod_apply, Function.prod]
  have hrf : ∀ x, r (f x) = x := by
    rintro ⟨a, b⟩
    obtain ⟨h1, h2, -, h4, h5, -⟩ := hax a
    obtain ⟨k1, k2, -, k4, k5, -⟩ := hax b
    have hf : f (a, b) = pF (fst A A) a + pF (snd A A) b := by simp [f]
    rw [hr, hf, map_add (f := _), map_add (f := _), h1, k2, h4, k5, add_zero, zero_add]
  have hbij := GlobalTheory.T.bijective_of_split_injective_fgProjectiveConstantRank R _ _ (g + g) hM hN f r hrf
  have hrinj : Function.Injective r := by
    intro y y' h
    obtain ⟨x, rfl⟩ := hbij.2 y
    obtain ⟨x', rfl⟩ := hbij.2 y'
    rw [hrf, hrf] at h; rw [h]
  intro x
  obtain ⟨-, -, h3, -, -, h6⟩ := hax x
  have e1 : r (pF μ[A] x) = (x, x) := (hr _).trans (Prod.ext h3 h6)
  exact (hrinj (e1.trans (hrf (x, x)).symm)).trans (LinearMap.coprod_apply _ _ _)

end GlobalTheory.AbCoh
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AbCoh.AxesForm

open GlobalTheory.AbCoh.PrimForm

theorem eq_zero_of_axes : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ y : GlobForm (A ⊗ A).hom, GlobalTheory.AbCoh.pF (lift (𝟙 A) (toUnit A ≫ η[A])) y = 0 → GlobalTheory.AbCoh.pF (lift (toUnit A ≫ η[A]) (𝟙 A)) y = 0 → y = 0 := by
  intro R _ A _ g hA hg y h₁ h₂
  obtain ⟨hA2, hg2⟩ := (GlobalTheory.T.abelian_square_affine_h1_vanish R).1 A g hA hg
  obtain ⟨f1, p1, r1⟩ := GlobalTheory.T.abelianScheme_global_oneForms_projective_rank R A g hA hg
  obtain ⟨f2, p2, r2⟩ := GlobalTheory.T.abelianScheme_global_oneForms_projective_rank R (A ⊗ A) (g + g) hA2 hg2
  let N : GlobForm (A ⊗ A).hom →ₗ[R] GlobForm A.hom × GlobForm A.hom :=
    LinearMap.prod (pF (lift (𝟙 A) (toUnit A ≫ η[A]))) (pF (lift (toUnit A ≫ η[A]) (𝟙 A)))
  let P : GlobForm A.hom × GlobForm A.hom →ₗ[R] GlobForm (A ⊗ A).hom :=
    LinearMap.coprod (pF (fst A A)) (pF (snd A A))
  have hNP : N ∘ₗ P = LinearMap.id := by
    refine LinearMap.ext fun x ↦ Prod.ext ?_ ?_
    · show pF (lift (𝟙 A) (toUnit A ≫ η[A])) (pF (fst A A) x.1 + pF (snd A A) x.2) = x.1
      rw [map_add (f := _), pF_comp, pF_comp, lift_fst, lift_snd, pF_id, pF_unit, add_zero]
    · show pF (lift (toUnit A ≫ η[A]) (𝟙 A)) (pF (fst A A) x.1 + pF (snd A A) x.2) = x.2
      rw [map_add (f := _), pF_comp, pF_comp, lift_fst, lift_snd, pF_id, pF_unit, zero_add]
  have hinj := GlobalTheory.Obs.Axes.injective_of_section N P hNP (fun p ↦ by
    rw [Module.rankAtStalk_prod, Pi.add_apply, r1, r2])
  refine hinj (?_ : N y = N 0)
  rw [map_zero]
  exact Prod.ext h₁ h₂

end GlobalTheory.AbCoh.AxesForm
end
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.weierstrassModel_unit_discriminant_away_from_p : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → sqProd p L t ∈ F → ∀ V : ValuationSubring ℂ, V.valuation (p : ℂ) = 1 → ModelAt V F (latticeCurve L) 1 := by
  first | exact @GlobalTheory.CMModel.modelAt_one_of_sqProd_mem | exact GlobalTheory.CMModel.modelAt_one_of_sqProd_mem | (intros; apply GlobalTheory.CMModel.modelAt_one_of_sqProd_mem <;> assumption)
end
