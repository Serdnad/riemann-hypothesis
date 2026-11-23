module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle851
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1698
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle864
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1161
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle866
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1657
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1736
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle999
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle875
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle819
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1589
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1756
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1596
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1602
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1588
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1400
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1737
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1480
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

@[expose] public section

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu

theorem omega_finite_of_theory (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (G : PDivGroup p k) : Module.Finite k G.omega := by
  classical
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_theta_dieudonne_mod_frobenius_differentials p T k
  obtain ⟨-, hs, -, hsm, -⟩ := hθ G
  haveI := T.base.finite G trivial
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule (WittVector p k) (T.M G)).FG)
  refine ⟨⟨S.image (θ G), ?_⟩⟩
  rw [Finset.coe_image, eq_top_iff]
  rintro y -
  obtain ⟨m, rfl⟩ := hs y
  have hm : m ∈ Submodule.span (WittVector p k) (S : Set (T.M G)) := hS ▸ Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [(θ G).map_add]; exact add_mem hx hy
  | smul a x _ hx =>
    obtain ⟨b, rfl⟩ : ∃ b, WittVector.frobenius b = a :=
      ⟨(WittVector.frobeniusEquiv p k).symm a, (WittVector.frobeniusEquiv p k).apply_symm_apply a⟩
    rw [hsm]
    exact Submodule.smul_mem _ _ hx

theorem range_omegaMap_le_of_range_map_le (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] {G Q H : PDivGroup p k} (q : G ⟶ Q) (f : G ⟶ H)
    (h : LinearMap.range (T.map f) ≤ LinearMap.range (T.map q)) :
    LinearMap.range (omegaMap G H f) ≤ LinearMap.range (omegaMap G Q q) := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_theta_dieudonne_mod_frobenius_differentials p T k
  rintro _ ⟨v, rfl⟩
  obtain ⟨m, rfl⟩ := (hθ H).2.1 v
  obtain ⟨m', hm'⟩ := h ⟨m, rfl⟩
  refine ⟨θ Q m', ?_⟩
  rw [← (hθ G).2.2.2.2 Q q m', ← (hθ G).2.2.2.2 H f m, hm']

theorem exists_comp_eq_of_colength (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (n : ℕ) : ∀ (G Q H : PDivGroup p k) (q : G ⟶ Q) (f : G ⟶ H),
    G.IsConn → IsIsog q →
    Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) = n →
    LinearMap.range (T.map f) ≤ LinearMap.range (T.map q) → ∃ g : Q ⟶ H, q ≫ g = f := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G Q H q f hG hq hn hfq
  have hω := range_omegaMap_le_of_range_map_le p T k q f hfq
  by_cases hsurj : Function.Surjective (omegaMap G Q q)
  · have hs := GlobalTheory.T.app_surjective_of_omegaMap_surjective_connected p k G Q q hG hsurj
    obtain ⟨m, q', h1, h2⟩ := hq
    refine GlobalTheory.T.pDivisibleGroup_exists_factor_through_isogeny p k G Q H m q q' f h1 h2 ?_
    rw [kerIdeal_of_surjective (hs m)]
    exact (kerIdeal_le_ker_iff _ _).2 fun c => by simp
  obtain ⟨C, i1, i2, i3, i4, π, hπs, hker, hnil, hfrob⟩ := GlobalTheory.T.exists_quotient_kernel_sup_frobeniusKernel p k G Q q
  obtain ⟨Q₁, q₁, q₁', e1, e2, hk1⟩ := GlobalTheory.T.exists_quotient_pDivGroup_closedSubgroup_pTorsion p k G C π hπs
  have hqπ : kerIdeal (q.app 1) ≤ RingHom.ker π := hker ▸ le_sup_left
  have hcq := GlobalTheory.T.cotangent_kernel_eq_coker_omegaMap p k G Q q C π hπs
  have hcq₁ := GlobalTheory.T.cotangent_kernel_eq_coker_omegaMap p k G Q₁ q₁ C π hπs
  have hcotf : cotMap (π.comp (f.app 1)) = 0 :=
    hcq.2.2 H f fun w hw => hcq.1 hqπ w (hω hw)
  have htriv := GlobalTheory.T.eq_counit_of_heightOne_cotangentPullback_zero p k C (H.A 1) (π.comp (f.app 1)) hnil hcotf
  have hfπ : kerIdeal (f.app 1) ≤ RingHom.ker π :=
    (kerIdeal_le_ker_iff (f.app 1) (π : G.A 1 →ₐ[k] C)).2 htriv
  have e1' : q₁ ≫ q₁' = (p : ℤ_[p]) ^ 1 • 𝟙 G := by rw [pow_one]; exact e1
  have e2' : q₁' ≫ q₁ = (p : ℤ_[p]) ^ 1 • 𝟙 Q₁ := by rw [pow_one]; exact e2
  obtain ⟨f', hf'⟩ := GlobalTheory.T.pDivisibleGroup_exists_factor_through_isogeny p k G Q₁ H 1 q₁ q₁' f e1' e2' (hk1 ▸ hfπ)
  obtain ⟨r, hr⟩ := GlobalTheory.T.pDivisibleGroup_exists_factor_through_isogeny p k G Q₁ Q 1 q₁ q₁' q e1' e2' (hk1 ▸ hqπ)
  have hq₁ : IsIsog q₁ := ⟨1, q₁', e1', e2'⟩
  have hr' : IsIsog r := (GlobalTheory.T.pDivisibleGroup_isogeny_basic_properties p k G).2.2.1 Q₁ Q q₁ r hq₁ (hr ▸ hq)
  have hG₁ : Q₁.IsConn := GlobalTheory.T.pDivGroup_isConn_of_isogeny p k G Q₁ q₁ hq₁ hG
  have hfun := GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k G Q₁ Q trivial trivial trivial
  have hfun' := GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k G Q₁ H trivial trivial trivial
  have hmq : T.map q = T.map q₁ ∘ₗ T.map r := by rw [← hr]; exact hfun.2.1 q₁ r
  have hmf : T.map f = T.map q₁ ∘ₗ T.map f' := by rw [← hf']; exact hfun'.2.1 q₁ f'
  have hinj := (GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k G Q₁ q₁ hq₁).1
  have hfr : LinearMap.range (T.map f') ≤ LinearMap.range (T.map r) := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := hfq ⟨y, rfl⟩
    refine ⟨z, hinj ?_⟩
    rw [← LinearMap.comp_apply, ← hmq, hz, hmf, LinearMap.comp_apply]

  haveI := omega_finite_of_theory p T k G
  have hCq : Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G Q q)) = Module.finrank k (Cot k C) :=
    hcq.2.1 (hker ▸ sup_le_sup_left hfrob _) hqπ
  have hCq₁ : Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G Q₁ q₁)) =
      Module.finrank k (Cot k C) := hcq₁.2.1 (hk1 ▸ le_sup_left) hk1.le
  have hpos : 0 < Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G Q q)) := by
    haveI : Nontrivial (G.omega ⧸ LinearMap.range (omegaMap G Q q)) :=
      Submodule.Quotient.nontrivial_iff.2 fun h => hsurj (LinearMap.range_eq_top.1 h)
    exact Module.finrank_pos
  have h1 : (1 : ℕ∞) ≤ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q₁)) := by
    refine le_trans ?_ (GlobalTheory.T.finrank_quot_range_le_length_quot_range_map p T k G Q₁ q₁).1
    rw [hCq₁, ← hCq]
    exact_mod_cast hpos
  have hadd := (GlobalTheory.T.witt_module_length_composition p k (T.M G) (T.M Q₁) (T.M Q)).1 (T.map q₁) (T.map r) hinj
  rw [← hmq, hn] at hadd
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 (show Module.length (WittVector p k)
      (T.M G ⧸ LinearMap.range (T.map q₁)) ≠ ⊤ from fun h => by simp [h] at hadd)
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1 (show Module.length (WittVector p k)
      (T.M Q₁ ⧸ LinearMap.range (T.map r)) ≠ ⊤ from fun h => by simp [h] at hadd)
  rw [← ha, ← hb] at hadd
  rw [← ha] at h1
  have hab : n = a + b := by exact_mod_cast hadd
  have ha1 : 1 ≤ a := by exact_mod_cast h1
  obtain ⟨g, hg⟩ := ih b (by omega) Q₁ Q H r f' hG₁ hr' hb.symm hfr
  exact ⟨g, by rw [← hr, Category.assoc, hg, hf']⟩

theorem exists_comp_eq_of_range_map_le : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (G Q H : PDivGroup p k) (q : G ⟶ Q) (f : G ⟶ H), G.IsConn →
    IsIsog q → LinearMap.range (T.map f) ≤ LinearMap.range (T.map q) → ∃ g : Q ⟶ H, q ≫ g = f := by
  intro p _ T k _ _ _ G Q H q f hG hq hfq
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k G Q q hq).2.1
  exact exists_comp_eq_of_colength p T k n G Q H q f hG hq hn.symm hfq

end GlobalTheory.Dieu
end
end

section

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology GlobalTheory.HCF

namespace GlobalTheory.AutGrowth.RankLocal

open GlobalTheory.AutGrowth.KilledFin GlobalTheory.AutGrowth.SmoothFinite

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem finite_forms (h : ∀ (L' : Subgroup (GL (Fin a) (Af E))), IsOpen (L' : Set (GL (Fin a) (Af E))) →
      ∀ W' : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W' →
      ∀ X' : Set (Module.End ℂ (Sm E a) → ℂ), X'.Finite → ∀ N' : ℕ,
        FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L' W' X' N')))
    (L : Subgroup (GL (Fin a) (Af E))) (hL : IsOpen (L : Set (GL (Fin a) (Af E))))
    (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W)
    (c : (E →+* ℂ) → ℂ → ℂ) :
    FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.Published.AutFinGL.forms L ρ c)) := by
  classical
  haveI hW' : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := GlobalTheory.T.finiteDimensional_matrixCoefficientSpan _ W ρ
  let χ : Module.End ℂ (Sm E a) → ℂ := fun z =>
    if hz : ∃ s : ℂ, ∀ φ : Sm E a, (∀ τ u, cap τ u φ = c τ u • φ) → z φ = s • φ then hz.choose else 0
  have hsub : GlobalTheory.Published.AutFinGL.forms L ρ c ⊆ formsGL E a L (GlobalTheory.Published.AutFin.coeffSpan ρ) {χ} 1 := by
    rintro φ ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, χ, rfl, ?_⟩
    intro zs hlen hzs
    match zs, hlen with
    | [z], _ =>
      have hz : z ∈ Zalg E a := hzs z (List.mem_singleton_self z)
      have hex := GlobalTheory.T.center_acts_by_scalar_on_eigenforms E a c z hz
      have hχ : χ z = hex.choose := dif_pos hex
      simp only [List.foldr_cons, List.foldr_nil]
      rw [hχ, hex.choose_spec φ h4, sub_self]
  have hfin := h L hL (GlobalTheory.Published.AutFin.coeffSpan ρ) hW' {χ} (Set.finite_singleton χ) 1
  exact Submodule.finiteDimensional_of_le (Submodule.span_mono hsub)

theorem finiteDimensional_capEigen_maps_rank (h : ∀ (L' : Subgroup (GL (Fin a) (Af E))), IsOpen (L' : Set (GL (Fin a) (Af E))) →
      ∀ W' : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W' →
      ∀ X' : Set (Module.End ℂ (Sm E a) → ℂ), X'.Finite → ∀ N' : ℕ,
        FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L' W' X' N')))
    (L : Subgroup (GL (Fin a) (Af E))) (hL : IsOpen (L : Set (GL (Fin a) (Af E))))
    (W : Submodule ℂ (Sm E a)) (hW : ∀ k, ∀ w ∈ W, cptRep E a k w ∈ W) (hWf : FiniteDimensional ℂ W)
    (c : (E →+* ℂ) → ℂ → ℂ) (N : Submodule ℂ (W →ₗ[ℂ] Sm E a)) (hN : N ≤ maps L W hW)
    (hcap : ∀ T ∈ N, ∀ τ u, cap τ u ∘ₗ T = c τ u • T) : FiniteDimensional ℂ N := by
  haveI := hWf
  have hF := finite_forms h L hL W (GlobalTheory.PRep.sub (cptRep E a) W hW) c
  haveI := hF
  have hmem : ∀ T ∈ N, ∀ w, T w ∈ GlobalTheory.Published.AutFinGL.forms L (GlobalTheory.PRep.sub (cptRep E a) W hW) c := by
    intro T hT w
    have hm : (∀ k w, T (GlobalTheory.PRep.sub (cptRep E a) W hW k w) = cptRep E a k (T w)) ∧
        ∀ w, T w ∈ tame E a ∧ (∀ γ g, (T w).1 (ratGL E a γ * g) = (T w).1 g) ∧
          ∀ k ∈ L, finRep E a k (T w) = T w := hN hT
    obtain ⟨heq, hall⟩ := hm
    obtain ⟨htame, hleft, hfix⟩ := hall w
    have hZ : ∀ z ∈ Zalg E a, ∃ s : ℂ, z ∘ₗ T = s • T := by
      intro z hz
      induction hz using Algebra.adjoin_induction with
      | mem x hx => obtain ⟨τ, u, rfl⟩ := hx; exact ⟨c τ u, hcap T hT τ u⟩
      | algebraMap r => exact ⟨r, LinearMap.ext fun v => by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨s, hs⟩ := hx
        obtain ⟨t, ht⟩ := hy
        exact ⟨s + t, by rw [LinearMap.add_comp, hs, ht, add_smul]⟩
      | mul x y _ _ hx hy =>
        obtain ⟨s, hs⟩ := hx
        obtain ⟨t, ht⟩ := hy
        exact ⟨t * s, by rw [Module.End.mul_eq_comp, LinearMap.comp_assoc, ht, LinearMap.comp_smul, hs, smul_smul]⟩
    refine ⟨⟨hleft, ?_, ?_, ?_, ?_⟩, hfix, GlobalTheory.Published.AutFinGL.type_of_map _ T heq w, fun τ u => ?_⟩
    · exact isOpen_stab_of_mem_nhds (finRep E a) (T w)
        (Filter.mem_of_superset (hL.mem_nhds L.one_mem) fun k hk => hfix k hk)
    · refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range T) (Submodule.span_le.2 ?_)
      rintro _ ⟨k, rfl⟩
      exact ⟨_, heq k w⟩
    · refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {T w}) (Submodule.span_le.2 ?_)
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨s, hs⟩ := hZ z hz
      have e : z (T w) = s • T w := LinearMap.congr_fun hs w
      show z (T w) ∈ _
      rw [e]
      exact Submodule.smul_mem _ s (Submodule.mem_span_singleton_self _)
    · exact growth_of_tame htame
    · exact LinearMap.congr_fun (hcap T hT τ u) w
  let Φ : N →ₗ[ℂ] (W →ₗ[ℂ] Submodule.span ℂ (GlobalTheory.Published.AutFinGL.forms L (GlobalTheory.PRep.sub (cptRep E a) W hW) c)) :=
    { toFun := fun T => LinearMap.codRestrict _ T.1 fun w => Submodule.subset_span (hmem T.1 T.2 w)
      map_add' := fun T T' => LinearMap.ext fun w => rfl
      map_smul' := fun r T => LinearMap.ext fun w => rfl }
  have hinj : Function.Injective Φ := fun T T' h =>
    Subtype.ext (LinearMap.ext fun w => congrArg Subtype.val (LinearMap.congr_fun h w))
  exact Module.Finite.of_injective Φ hinj

theorem finiteDimensional_mapsJ_rank (h : ∀ (L' : Subgroup (GL (Fin a) (Af E))), IsOpen (L' : Set (GL (Fin a) (Af E))) →
      ∀ W' : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W' →
      ∀ X' : Set (Module.End ℂ (Sm E a) → ℂ), X'.Finite → ∀ N' : ℕ,
        FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L' W' X' N')))
    (φ : Sm E a) (hφ : IsAutForm φ) (L : Subgroup (GL (Fin a) (Af E)))
    (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) : FiniteDimensional ℂ (mapsJ φ L) := by
  have hcap : ∀ (τ : E →+* ℂ) (u : ℂ), cap (a := a) τ u ∈ Zalg E a := fun τ u =>
    Algebra.subset_adjoin ⟨τ, u, rfl⟩
  let S : Set (Module.End ℂ (mapsJ φ L)) := {s | ∃ τ u, s = postZ φ L (cap τ u) (hcap τ u)}
  refine GlobalTheory.T.finiteDimensional_of_commuting_finiteAlgebra_jointEigen (mapsJ φ L) S ?_ ?_ ?_
  · rintro _ ⟨τ, u, rfl⟩ _ ⟨τ', u', rfl⟩
    refine LinearMap.ext fun T => Subtype.ext (LinearMap.ext fun w => ?_)
    show cap τ u (cap τ' u' (T.1 w)) = cap τ' u' (cap τ u (T.1 w))
    rw [← Module.End.mul_apply, (Zalg_commute (hcap τ u) (hcap τ' u')).eq, Module.End.mul_apply]
  · let ev : Zalg E a →ₗ[ℂ] Sm E a := (LinearMap.applyₗ φ).comp (Zalg E a).val.toLinearMap
    have hker : LinearMap.ker ev ≤ LinearMap.ker (postZAlg φ L).toLinearMap := by
      intro z hz
      rw [LinearMap.mem_ker] at hz ⊢
      refine LinearMap.ext fun T => Subtype.ext (LinearMap.ext fun w => ?_)
      have hT : T.1 ∈ maps L (spanK E a φ) (spanK_stable φ) ∧
          ∀ z ∈ Zalg E a, z φ = 0 → ∀ w, z (T.1 w) = 0 := T.2
      exact hT.2 z.1 z.2 hz w
    have hev : FiniteDimensional ℂ (LinearMap.range ev) := by
      have h1 : LinearMap.range ev ≤
          Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) := by
        rintro _ ⟨z, rfl⟩
        exact Submodule.subset_span ⟨z.1, z.2, rfl⟩
      haveI := hφ.zfin
      exact Submodule.finiteDimensional_of_le h1
    refine fd_adjoin_of_ker_le (mapsJ φ L) (Zalg E a) (Sm E a) (postZAlg φ L) ev hev hker S ?_
    rintro _ ⟨τ, u, rfl⟩
    exact ⟨⟨cap τ u, hcap τ u⟩, rfl⟩
  · intro c
    let J := ⨅ s ∈ S, LinearMap.ker (s - algebraMap ℂ (Module.End ℂ (mapsJ φ L)) (c s))
    let N : Submodule ℂ (spanK E a φ →ₗ[ℂ] Sm E a) := J.map (mapsJ φ L).subtype
    have hNle : N ≤ maps L (spanK E a φ) (spanK_stable φ) := by
      rintro _ ⟨T, _, rfl⟩
      have hT : T.1 ∈ maps L (spanK E a φ) (spanK_stable φ) ∧
          ∀ z ∈ Zalg E a, z φ = 0 → ∀ w, z (T.1 w) = 0 := T.2
      exact hT.1
    have hNe : ∀ T ∈ N, ∀ (τ : E →+* ℂ) (u : ℂ),
        cap τ u ∘ₗ T = c (postZ φ L (cap τ u) (hcap τ u)) • T := by
      rintro _ ⟨T, hT, rfl⟩ τ u
      have hT' : T ∈ ⨅ s ∈ S, LinearMap.ker (s - algebraMap ℂ (Module.End ℂ (mapsJ φ L)) (c s)) := hT
      have h₀ := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hT' (postZ φ L (cap τ u) (hcap τ u))) ⟨τ, u, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Module.algebraMap_end_apply] at h₀
      exact congrArg Subtype.val h₀
    have hN : FiniteDimensional ℂ N :=
      finiteDimensional_capEigen_maps_rank h L hL (spanK E a φ) (spanK_stable φ) hφ.kfin
        (fun τ u => c (postZ φ L (cap τ u) (hcap τ u))) N hNle hNe
    exact LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective (mapsJ φ L).subtype Subtype.val_injective J).symm

theorem exists_finite_space_rank (h : ∀ (L' : Subgroup (GL (Fin a) (Af E))), IsOpen (L' : Set (GL (Fin a) (Af E))) →
      ∀ W' : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W' →
      ∀ X' : Set (Module.End ℂ (Sm E a) → ℂ), X'.Finite → ∀ N' : ℕ,
        FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L' W' X' N')))
    (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (φ : Sm E a) (hφ : IsAutForm φ) :
    ∃ V : Submodule ℂ (Sm E a), FiniteDimensional ℂ V ∧ V ≤ tame E a ∧ ∀ α, IsTest (invSet E a) α → KInv α →
      ∃ h : smoothing ν α φ.1 ∈ Sm E a, (⟨smoothing ν α φ.1, h⟩ : Sm E a) ∈ V := by
  let w0 : spanK E a φ := ⟨φ, self_mem_spanK φ⟩
  haveI := finiteDimensional_mapsJ_rank h φ hφ (stabL φ) hφ.level
  refine ⟨(mapsJ φ (stabL φ)).map (LinearMap.applyₗ w0), inferInstance, ?_, fun α hα hK =>
    ⟨GlobalTheory.T.realLieSmoothing_mem_smoothAdelicFunctions E a ν α hα φ.1 φ.2, smoothMap ν hα _, smoothMap_mem ν hα hK hφ, rfl⟩⟩
  rintro _ ⟨T, hT, rfl⟩
  exact (hT.1.2 w0).1

theorem tame_of_autForm_rank : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ),
    (∀ (L' : Subgroup (GL (Fin n) (Af E))), IsOpen (L' : Set (GL (Fin n) (Af E))) →
      ∀ W' : Submodule ℂ (Kinf E n → ℂ), FiniteDimensional ℂ W' →
      ∀ X' : Set (Module.End ℂ (Sm E n) → ℂ), X'.Finite → ∀ N' : ℕ,
        FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E n L' W' X' N'))) →
    ∀ φ : Sm E n, IsAutForm φ → φ ∈ GlobalTheory.AutGrowth.tame E n := by
  intro E _ _ _ a hfin φ hφ
  let ν : Measure (Lie E a) := Measure.addHaar
  obtain ⟨α, hα, hlim⟩ := GlobalTheory.T.exists_conjInvariant_approxIdentity_realLieSmoothing E a ν
  obtain ⟨V, hVf, hVt, hV⟩ := exists_finite_space_rank hfin ν φ hφ
  let V' : Submodule ℂ (GA E a → ℂ) := V.map (Sm E a).subtype
  have hc : IsClosed (V' : Set (GA E a → ℂ)) := Submodule.closed_of_finiteDimensional V'
  have hmem : ∀ n, smoothing ν (α n) φ.1 ∈ V' := fun n => by
    obtain ⟨h, hv⟩ := hV (α n) (hα n).1 (hα n).2
    exact ⟨_, hv, rfl⟩
  have hφ' : φ.1 ∈ V' :=
    hc.mem_of_tendsto (tendsto_pi_nhds.2 fun g => hlim φ.1 φ.2 g) (Eventually.of_forall hmem)
  obtain ⟨ψ, hψ, e⟩ := hφ'
  have e' : ψ = φ := Subtype.ext e
  exact hVt (e' ▸ hψ)

end GlobalTheory.AutGrowth.RankLocal

end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef.TorExt

theorem algebraMap_comp_C (Ω : Type) [Field Ω] :
    (algebraMap (RatFunc Ω) (LaurentSeries Ω)).comp RatFunc.C =
      (algebraMap (PowerSeries Ω) (LaurentSeries Ω)).comp PowerSeries.C := by
  refine RingHom.ext fun c => ?_
  simp only [RingHom.comp_apply]
  rw [← RatFunc.algebraMap_C]
  have := RatFunc.coe_coe (Polynomial.C c)
  simp only [Polynomial.coe_C] at this
  exact this.symm

theorem unitSec_comp {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H) [IsMonHom f] :
    unitSec G ≫ f.left = unitSec H := by
  rw [unitSec, unitSec, sec, sec, ← Over.comp_left, IsMonHom.one_hom]

theorem isLocalHom_field {K L : Type} [Field K] [Field L] (φ : K →+* L) : IsLocalHom φ :=
  ⟨fun x hx => by
    by_cases h : x = 0
    · subst h; simp at hx
    · exact IsUnit.mk0 x h⟩

theorem exists_lift {Ω : Type} [Field Ω] {G : Over (Sp Ω)} [GrpObj G] (E : TorusExtension G) {Z : Scheme.{0}}
    (z : Z ⟶ Sp Ω) (f : Z ⟶ G.left) (hf : f ≫ G.hom = z) (hq : letI := E.grpB; f ≫ E.q.left = z ≫ unitSec E.B) :
    letI := E.addCommGroup
    ∃ g : Z ⟶ (splitTorus (Sp Ω) E.X).left, g ≫ E.i.left = f ∧ g ≫ (splitTorus (Sp Ω) E.X).hom = z := by
  letI := E.addCommGroup
  letI := E.grpB
  let f' : Over.mk z ⟶ G := Over.homMk f hf
  have h : f' ≫ E.q = toUnit _ ≫ η := by
    ext
    simp [f', hq, unitSec, sec]
  refine ⟨(E.isKernel.lift f' (toUnit _) h).left, ?_, ?_⟩
  · rw [← Over.comp_left, E.isKernel.lift_fst]
    rfl
  · exact Over.w (E.isKernel.lift f' (toUnit _) h)

theorem mono_i {Ω : Type} [Field Ω] {G : Over (Sp Ω)} [GrpObj G] (E : TorusExtension G) :
    letI := E.addCommGroup
    Mono E.i.left := by
  letI := E.addCommGroup
  letI := E.grpB
  have : Mono E.i := ⟨fun a b hab => E.isKernel.hom_ext hab (toUnit_unique _ _)⟩
  exact Over.mono_left_of_mono _

end GlobalTheory.Nef.TorExt

namespace GlobalTheory.Nef


open TorExt in
theorem ratRigid_of_torusExtension : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (G : Over (Sp Ω)) [GrpObj G],
    Nonempty (TorusExtension G) → RatRigid G (𝟙 (Sp Ω)) := by
  intro Ω _ _ G _ ⟨E⟩ ξ hξ ⟨β, hβ⟩
  letI := E.addCommGroup
  letI := E.grpB
  haveI := E.q_hom
  haveI := E.i_hom
  haveI : IsProper E.B.hom := E.isAbelian.proper
  haveI := mono_i E
  haveI := isLocalHom_field (algebraMap (RatFunc Ω) (LaurentSeries Ω))
  obtain ⟨-, bc2⟩ := GlobalTheory.T.formalSquaringPaths_baseChange_and_hom
  obtain ⟨epi1, -⟩ := GlobalTheory.T.spec_injectiveRingMap_cancellation
  set T := splitTorus (Sp Ω) E.X
  set a := algebraMap (RatFunc Ω) (LaurentSeries Ω)
  set ι₀ := algebraMap (PowerSeries Ω) (LaurentSeries Ω)
  have ha : Function.Injective a := a.injective
  have hC : spMap a ≫ spMap RatFunc.C = spMap ι₀ ≫ spMap (PowerSeries.C (R := Ω)) := by
    rw [← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp, algebraMap_comp_C]
  have hq : ξ ≫ E.q.left = spMap (PowerSeries.C (R := Ω)) ≫ unitSec E.B := by
    have := GlobalTheory.T.rationalSquaringPathsRigid_of_proper_charZero Ω E.B inferInstance (ξ ≫ E.q.left) ((bc2 _ G E.B E.q Ω 2 (𝟙 _) ξ).1 hξ)
      ⟨β ≫ E.q.left, by rw [← Category.assoc, hβ, Category.assoc]⟩
    rw [this, triv, Category.id_comp]
  have hbase : ξ ≫ G.hom = spMap (PowerSeries.C (R := Ω)) := by
    rw [hξ.base, Category.comp_id]
  obtain ⟨ζ, hζ, hζT⟩ := exists_lift E _ ξ hbase hq
  have hβG : β ≫ G.hom = spMap (RatFunc.C (K := Ω)) :=
    epi1 _ _ a ha _ _ _ (by rw [reassoc_of% hβ, hbase, hC])
  have hβq : β ≫ E.q.left = spMap (RatFunc.C (K := Ω)) ≫ unitSec E.B :=
    epi1 _ _ a ha _ _ _ (by rw [reassoc_of% hβ, hq, reassoc_of% hC])
  obtain ⟨βT, hβT, -⟩ := exists_lift E _ β hβG hβq
  have hTunit : unitSec T ≫ E.i.left = unitSec G := unitSec_comp E.i
  have hpath : IsPath T 2 (𝟙 _) ζ := by
    refine ⟨by rw [hζT, Category.comp_id], ?_, ?_⟩
    · rw [← cancel_mono E.i.left, Category.assoc, hζ, hξ.zero, Category.assoc, hTunit]
    · rw [← cancel_mono E.i.left, Category.assoc, hζ, hξ.scale, Category.assoc,
        (bc2 _ T G E.i Ω 2 (𝟙 _) ζ).2.2, reassoc_of% hζ]
  have hrat : IsRatPath ζ :=
    ⟨βT, by rw [← cancel_mono E.i.left, Category.assoc, hβT, hβ, Category.assoc, hζ]⟩
  have h := GlobalTheory.T.splitTorus_rationalSquaringPathsRigid_charZero Ω E.X ζ hpath hrat
  rw [← hζ, h, (bc2 _ T G E.i Ω 2 (𝟙 _) ζ).2.1]

end GlobalTheory.Nef
end
end
