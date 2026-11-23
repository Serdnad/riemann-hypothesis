module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle892
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle731
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle852
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle905
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle883
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle885
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle884
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.dual_isConn_of_isEt_pDivGroup : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), G.IsEt → G.dual.IsConn := by
  first | exact @GlobalTheory.PDivGroup.dual_isConn_of_isEt | exact GlobalTheory.PDivGroup.dual_isConn_of_isEt | (intros; apply GlobalTheory.PDivGroup.dual_isConn_of_isEt <;> assumption)
end

section

set_option autoImplicit false

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

namespace PDivGroup

theorem exists_isConn_isEt_splitting :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k),
      ∃ (G₀ G₁ : PDivGroup p k) (i₀ : G₀ ⟶ G) (q₀ : G ⟶ G₀) (i₁ : G₁ ⟶ G) (q₁ : G ⟶ G₁),
        G₀.IsConn ∧ G₁.IsEt ∧ i₀ ≫ q₀ = 𝟙 G₀ ∧ i₁ ≫ q₁ = 𝟙 G₁ ∧ q₀ ≫ i₀ + q₁ ≫ i₁ = 𝟙 G := by
  intro p _ k _ _ _ G
  obtain ⟨e, he, hnil, hred⟩ := GlobalTheory.T.exists_idempotent_nilpotent_complement_of_perfect p k G
  have h1 : e + (𝟙 G - e) = 𝟙 G := add_sub_cancel _ _
  have h1' : (𝟙 G - e) + e = 𝟙 G := sub_add_cancel _ _
  have h2 : e ≫ (𝟙 G - e) = 0 := by rw [Preadditive.comp_sub, Category.comp_id, he, sub_self]
  have h3 : (𝟙 G - e) ≫ e = 0 := by rw [Preadditive.sub_comp, Category.id_comp, he, sub_self]
  obtain ⟨G₀, i₀, q₀, a₀, b₀, c₀⟩ := GlobalTheory.T.pDivGroup_idempotent_split_field p k G e (𝟙 G - e) h1 h2 h3
  obtain ⟨G₁, i₁, q₁, a₁, b₁, c₁⟩ := GlobalTheory.T.pDivGroup_idempotent_split_field p k G (𝟙 G - e) e h1' h3 h2
  refine ⟨G₀, G₁, i₀, q₀, i₁, q₁, fun n x hx => ?_, fun n => ⟨fun x hx => ?_⟩, a₀, a₁,
    by rw [b₀, b₁, h1']⟩
  · obtain ⟨a, rfl⟩ := (c₀ n).1 x
    have ha : a ∈ augIdeal k (G.A n) := by
      have hx' : counit (R := k) (i₀.app n a) = 0 := hx
      rw [CoalgHomClass.counit_comp_apply] at hx'
      exact hx'
    have hk : e.app n a ∈ RingHom.ker (i₀.app n) := by
      rw [(c₀ n).2]
      exact Ideal.mem_map_of_mem (e.app n : G.A n →ₐ[k] G.A n) ha
    have := (hnil n a).map (i₀.app n)
    rwa [map_sub, RingHom.mem_ker.1 hk, sub_zero] at this
  · obtain ⟨a, rfl⟩ := (c₁ n).1 x
    have hq : q₁.app n (i₁.app n a) = e.app n a := congrArg (fun g : G ⟶ G => g.app n a) b₁
    have hi : i₁.app n (q₁.app n (i₁.app n a)) = i₁.app n a :=
      congrArg (fun g : G₁ ⟶ G₁ => g.app n (i₁.app n a)) a₁
    have h0 : e.app n a = 0 := hred n a (hq ▸ hx.map (q₁.app n))
    rw [← hi, hq, h0, map_zero]

end PDivGroup

end GlobalTheory
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

namespace GlobalTheory

namespace PDivGroup

theorem rigExtMap_dualHom_eq_zero_of_isEt :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]
      (G H : PDivGroup p k) (f : G ⟶ H), G.IsEt → H.IsEt → rigExtMap f = 0 →
      rigExtMap (dualHom G H f) = 0 := by
  intro p _ k _ _ _ G H f hG hH hf
  have hp : (p : k) = 0 := CharP.cast_eq_zero k p
  obtain ⟨hH1, -⟩ := rigToLie_bijective_and_dual_rigOfOmega_bijective_of_isEt p k hp H hH
  obtain ⟨-, hG2⟩ := rigToLie_bijective_and_dual_rigOfOmega_bijective_of_isEt p k hp G hG

  have hlie : ∀ y : H.dual.Lie, lieMap H.dual G.dual (dualHom G H f) y = 0 := by
    intro y
    obtain ⟨x, rfl⟩ := hH1.2 y
    rw [← rigToLie_rigExtMap hp f x, hf, LinearMap.zero_apply, map_zero]

  have hom : ∀ w : G.dual.omega, omegaMap H.dual G.dual (dualHom G H f) w = 0 := by
    intro w
    refine (Module.forall_dual_apply_eq_zero_iff k _).1 fun y => ?_
    exact LinearMap.congr_fun (hlie y) w
  refine LinearMap.ext fun z => ?_
  obtain ⟨w, rfl⟩ := hG2.2 z
  rw [rigExtMap_rigOfOmega, hom, map_zero, LinearMap.zero_apply]

end PDivGroup

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem exists_prim_of_isPer : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ x q,
    IsPer u.ex u.Λ x q → ∀ c, Hyp1.mk _ c = x → ∃ h, IsPrim u.ex c h ∧
      ∀ (U : A.left.affineOpens) (l : u.Λ), ∀ z ∈ pre u.ex U.1, h U (z + l) = h U z + q l := by
  intro A _ g L u x q hx c hc
  obtain ⟨hOpen, hDiff, -, hPer, -, -, -, -, hRes, hHom, -, -⟩ := GlobalTheory.CechPer.pre_val_rules A g L u
  obtain ⟨c₀, h₀, hc₀, ⟨p1, p2, p3⟩, hp⟩ := hx
  obtain ⟨b, hb⟩ := Hyp1.mk_eq_mk.1 (hc.trans hc₀.symm)
  have hval_add : ∀ (U : A.left.Opens) (s t : Sec (str A) U), ∀ z ∈ pre u.ex U,
      val u.ex U (s + t) z = val u.ex U s z + val u.ex U t z := by
    intro U s t z hz
    obtain ⟨e, he⟩ := hHom U z hz
    erw [he, he, he, map_add]
  have hval_sub : ∀ (U : A.left.Opens) (s t : Sec (str A) U), ∀ z ∈ pre u.ex U,
      val u.ex U (s - t) z = val u.ex U s z - val u.ex U t z := by
    intro U s t z hz
    obtain ⟨e, he⟩ := hHom U z hz
    erw [he, he, he, map_sub]
  have hcf : ∀ (U V : A.left.affineOpens) (a : Opposite.op U ⟶ Opposite.op V),
      c.1.1 (Opposite.op U) (Opposite.op V) a = c₀.1.1 (Opposite.op U) (Opposite.op V) a +
        (b (Opposite.op V) - Sec.res (str A) (leOfHom a.unop) (b (Opposite.op U))) := by
    intro U V a
    have := congrArg (fun y : Tot1 (OAff (str A)) ↦ y.1 (Opposite.op U) (Opposite.op V) a) hb
    simp only [dTot0_f] at this
    exact (eq_add_of_sub_eq' this.symm :)
  have hcω : ∀ U : A.left.affineOpens, c.1.2 (Opposite.op U) =
      c₀.1.2 (Opposite.op U) + KaehlerDifferential.D ℂ _ (b (Opposite.op U)) := by
    intro U
    have := congrArg (fun y : Tot1 (OAff (str A)) ↦ y.2 (Opposite.op U)) hb
    simp only [dTot0_ω] at this
    change _ = (c.1 - c₀.1).2 _ at this
    rw [this]
    change c.1.2 _ = c₀.1.2 _ + (c.1.2 _ - c₀.1.2 _)
    abel
  refine ⟨fun U z ↦ h₀ U z + val u.ex U.1 (b (Opposite.op U)) z, ⟨fun U ↦ ?_, fun U V a z hz ↦ ?_, fun U z hz ↦ ?_⟩,
    fun U l z hz ↦ ?_⟩
  · exact (p1 U).add (hDiff U.1 _)
  · have hle : V.1 ≤ U.1 := leOfHom a.unop
    have hr : val u.ex V.1 (Sec.res (str A) hle (b (Opposite.op U))) z = val u.ex U.1 (b (Opposite.op U)) z :=
      hRes U.1 V.1 hle _ z hz
    simp only
    rw [p2 U V a z hz, hcf U V a, hval_add _ _ _ z hz, hval_sub _ _ _ z hz, hr]
    ring
  · have hd₀ : DifferentiableAt ℂ (h₀ U) z := ((p1 U) z hz).differentiableAt ((hOpen U.1).mem_nhds hz)
    have hd₁ : DifferentiableAt ℂ (val u.ex U.1 (b (Opposite.op U))) z :=
      ((hDiff U.1 _) z hz).differentiableAt ((hOpen U.1).mem_nhds hz)
    obtain ⟨-, -, hD⟩ := GlobalTheory.T.uniformisedOneFormEvaluation_rules A g L u U.1 z hz
    change fderiv ℂ (h₀ U + val u.ex U.1 (b (Opposite.op U))) z = _
    rw [fderiv_add hd₀ hd₁, p3 U z hz, hcω U, map_add (f := _), hD]
  · simp only
    rw [hp U l z hz]
    erw [hPer]
    ring

end GlobalTheory.CechPer
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem le_iSup_of_pre_cover : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens) (K : Type) (W : K → A.left.Opens), (∀ z ∈ pre u.ex U, ∃ i, z ∈ pre u.ex (W i)) → U ≤ ⨆ i, W i := by
  intro A _ g L u hA U K W h x hx
  obtain ⟨-, -, -, -, hinf, hmono, hsup, -, -, -, hbasic, -⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  obtain ⟨V, hV, hxV, hVU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp A.left.isBasis_affineOpens hx
  have hV' : IsAffineOpen V := hV
  let p : Ideal Γ(A.left, V) :=
    (IsLocalRing.maximalIdeal (A.left.presheaf.stalk x)).comap (A.left.presheaf.germ V x hxV).hom
  have hp : p ≠ ⊤ := Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p hp
  obtain ⟨z, hzV, hz⟩ := GlobalTheory.T.maximalIdeal_affineOpen_eq_vanishing_uniformisationPoint A g L u hA V hV' m hm
  obtain ⟨i, hi⟩ := h z (hmono U V hVU hzV)
  have hzi : z ∈ pre u.ex (W i ⊓ V) := by rw [hinf]; exact ⟨hi, hzV⟩
  have hle : W i ⊓ V ≤ ⨆ b : {b : Γ(A.left, V) // A.left.basicOpen b ≤ W i}, A.left.basicOpen b.1 := by
    intro y hy
    obtain ⟨f, hf, hyf⟩ := hV'.exists_basicOpen_le (V := W i) ⟨y, hy.1⟩ hy.2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, hf⟩, hyf⟩
  obtain ⟨⟨b, hb⟩, hzb⟩ := (hsup _ _ z).mp (hmono _ _ hle hzi)
  have hbm : b ∉ m := fun hh ↦ (hbasic V b z).mp hzb ((hz b).mp hh)
  have hxb : x ∈ A.left.basicOpen b := by
    rw [Scheme.mem_basicOpen _ b x hxV]
    by_contra hn
    exact hbm (hpm (Ideal.mem_comap.mpr ((IsLocalRing.mem_maximalIdeal _).mpr hn)))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hb hxb⟩

end GlobalTheory.CechPer
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.CechPer

theorem evForm_secPull : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (A' : Over (Sp ℂ)) [GrpObj A'] (g' : ℕ) (L' : LB A'.left) (u' : HolUnif A' L' g') (φ : A' ⟶ A) (M : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) (h : φ.left ≫ str A = str A' ≫ spMap (RingHom.id ℂ)), (∀ w, u.ex (M w) = u'.ex w ≫ φ) → ∀ (p : Pair φ.left), ∀ z ∈ pre u'.ex p.1.1.1, M z ∈ pre u.ex p.1.2.1 ∧ (∀ b, val u'.ex p.1.1.1 (secPull (str A) (str A') p b) z = val u.ex p.1.2.1 b (M z)) ∧ ∀ ξ, evForm u'.ex p.1.1.1 z ((semiHom_secPull h p).m1 ξ) = (evForm u.ex p.1.2.1 (M z) ξ).comp M := by
  intro A _ g L u A' _ g' L' u' φ M h hM p z hz
  have hpt : ∀ w, (u.ex (M w)).left = (u'.ex w).left ≫ φ.left := fun w => by rw [hM w]; rfl
  have hval : ∀ w ∈ pre u'.ex p.1.1.1, ∀ b, val u'.ex p.1.1.1 (secPull (str A) (str A') p b) w =
      val u.ex p.1.2.1 b (M w) := by
    intro w hw b
    have k := valAt'_appLE (u'.ex w).left φ.left p.1.2.1 p.1.1.1 p.2 b hw
    rw [← hpt] at k
    exact k
  have hpre : ∀ w ∈ pre u'.ex p.1.1.1, M w ∈ pre u.ex p.1.2.1 := by
    intro w hw
    change ⊤ ≤ (u.ex (M w)).left ⁻¹ᵁ p.1.2.1
    rw [hpt, top_le_preimage_comp]
    exact fun x hx => p.2 (hw hx)
  refine ⟨hpre z hz, hval z hz, ?_⟩
  have hopen : ∀ U, IsOpen (pre u.ex U) := fun U => (u.hol U 0).1
  have hdiff : ∀ U b, DifferentiableOn ℂ (val u.ex U b) (pre u.ex U) := fun U b => (u.hol U b).2
  have hopen' : ∀ U, IsOpen (pre u'.ex U) := fun U => (u'.hol U 0).1
  obtain ⟨-, hsm, hD⟩ := GlobalTheory.T.uniformisedOneFormEvaluation_rules A g L u p.1.2.1 (M z) (hpre z hz)
  obtain ⟨-, hsm', hD'⟩ := GlobalTheory.T.uniformisedOneFormEvaluation_rules A' g' L' u' p.1.1.1 z hz
  intro ξ
  have hξ : ξ ∈ Submodule.span (Sec (str A) p.1.2.1) (Set.range (KaehlerDifferential.D ℂ (Sec (str A) p.1.2.1))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hξ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    rw [SemiHom.m1_D, hD', hD]
    have e : val u'.ex p.1.1.1 (secPull (str A) (str A') p b) =ᶠ[nhds z] (val u.ex p.1.2.1 b) ∘ M :=
      Filter.eventually_of_mem ((hopen' p.1.1.1).mem_nhds hz) fun w hw => hval w hw b
    rw [e.fderiv_eq, fderiv_comp z ((hdiff _ b).differentiableAt ((hopen _).mem_nhds (hpre z hz)))
      M.differentiableAt, M.fderiv]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), ContinuousLinearMap.add_comp]
  | smul a x _ hx => rw [SemiHom.oneFormMap_smul_semilinear, hsm', hsm, hx, hval z hz a, ContinuousLinearMap.smul_comp]

end GlobalTheory.CechPer
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem uniformisedOneFormEvaluation_restriction_eq : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (U V : A.left.affineOpens) (a : Opposite.op U ⟶ Opposite.op V) (ξ : Ω[Sec (str A) U.1⁄ℂ]), ∀ z ∈ pre u.ex V.1, evForm u.ex V.1 z (p1 (OAff (str A)) a ξ) = evForm u.ex U.1 z ξ := by
  intro A _ g L u U V a ξ z hz
  obtain ⟨hopen, -, -, -, -, hmono, -, -, hres, -, -, -⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  have hVU : V.1 ≤ U.1 := leOfHom a.unop
  have hzU : z ∈ pre u.ex U.1 := hmono _ _ hVU hz
  have evV := GlobalTheory.T.uniformisedOneFormEvaluation_rules A g L u V.1 z hz
  have evU := GlobalTheory.T.uniformisedOneFormEvaluation_rules A g L u U.1 z hzU
  have hD : ∀ b : Sec (str A) U.1, fderiv ℂ (val u.ex V.1 (Sec.res (str A) hVU b)) z = fderiv ℂ (val u.ex U.1 b) z := by
    intro b
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [(hopen V.1).mem_nhds hz] with w hw
    exact hres _ _ hVU b w hw
  have hξ : ξ ∈ Submodule.span (Sec (str A) U.1) (Set.range (KaehlerDifferential.D ℂ (Sec (str A) U.1))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hξ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    rw [p1_D, evV.2.2, evU.2.2]
    exact hD b
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add (f := _), hx, hy]
  | smul b x _ hx =>
    rw [oneFormsMapOfFunctorMorphism_smul, evV.2.1, evU.2.1, hx]
    congr 1
    exact hres _ _ hVU b z hz

end GlobalTheory.CechPer
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem exists_section_of_isReg_sub : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g),
    IsAbelianScheme A → ∀ (K : Type) (W : K → A.left.Opens) (h : K → (Fin g → ℂ) → ℂ), ⨆ i, W i = ⊤ →
    (∀ i j, IsReg u.ex (W i ⊓ W j) (h i - h j)) → ∀ U : A.left.affineOpens, ∃ k : (Fin g → ℂ) → ℂ,
    ∀ i, IsReg u.ex (U.1 ⊓ W i) (k - h i) := by
  intro A _ g L u hA K W h hcov hreg U
  obtain ⟨-, -, -, -, hinf, -, -, -, hres, he, -, -⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  have hres' : ∀ (V V' : A.left.Opens) (hle : V' ≤ V) (b : Γ(A.left, V)), ∀ z ∈ pre u.ex V',
      val u.ex V' ((A.left.presheaf.map (homOfLE hle).op).hom b) z = val u.ex V b z :=
    fun V V' hle b z hz ↦ hres V V' hle b z hz
  have vsub : ∀ (V : A.left.Opens) (b c : Γ(A.left, V)), ∀ z ∈ pre u.ex V,
      val u.ex V (b - c) z = val u.ex V b z - val u.ex V c z := by
    intro V b c z hz
    obtain ⟨e, he'⟩ := he V z hz
    rw [he', he', he']
    exact map_sub e (show Sec (str A) V from b) c
  have vadd : ∀ (V : A.left.Opens) (b c : Γ(A.left, V)), ∀ z ∈ pre u.ex V,
      val u.ex V (b + c) z = val u.ex V b z + val u.ex V c z := by
    intro V b c z hz
    obtain ⟨e, he'⟩ := he V z hz
    rw [he', he', he']
    exact map_add e (show Sec (str A) V from b) c
  have vneg : ∀ (V : A.left.Opens) (b : Γ(A.left, V)), ∀ z ∈ pre u.ex V,
      val u.ex V (-b) z = - val u.ex V b z := by
    intro V b z hz
    obtain ⟨e, he'⟩ := he V z hz
    rw [he', he']
    exact map_neg e (show Sec (str A) V from b)
  choose b hb using hreg
  have hle : ∀ i j, (U.1 ⊓ W i) ⊓ (U.1 ⊓ W j) ≤ W i ⊓ W j :=
    fun i j ↦ inf_le_inf inf_le_right inf_le_right
  let f : ∀ i j, Γ(A.left, (U.1 ⊓ W i) ⊓ (U.1 ⊓ W j)) := fun i j ↦
    (A.left.presheaf.map (homOfLE (hle i j)).op).hom (b i j)
  have hf : ∀ i j, ∀ z ∈ pre u.ex ((U.1 ⊓ W i) ⊓ (U.1 ⊓ W j)), val u.ex _ (f i j) z = h i z - h j z := by
    intro i j z hz
    rw [hres' _ _ (hle i j) (b i j) z hz]
    have hz' : z ∈ pre u.ex (W i ⊓ W j) := (hinf _ _).symm ▸ (by
      rw [hinf, hinf, hinf] at hz
      exact ⟨hz.1.2, hz.2.2⟩)
    rw [← hb i j z hz']
    rfl
  have hcoc : ∀ i j k, (A.left.presheaf.map (homOfLE (inf_le_left : (U.1 ⊓ W i) ⊓ (U.1 ⊓ W j) ⊓ (U.1 ⊓ W k) ≤
        (U.1 ⊓ W i) ⊓ (U.1 ⊓ W j))).op).hom (f i j) +
      (A.left.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        (U.1 ⊓ W i) ⊓ (U.1 ⊓ W j) ⊓ (U.1 ⊓ W k) ≤ (U.1 ⊓ W j) ⊓ (U.1 ⊓ W k))).op).hom (f j k) =
      (A.left.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        (U.1 ⊓ W i) ⊓ (U.1 ⊓ W j) ⊓ (U.1 ⊓ W k) ≤ (U.1 ⊓ W i) ⊓ (U.1 ⊓ W k))).op).hom (f i k) := by
    intro i j k
    rw [← sub_eq_zero]
    refine GlobalTheory.T.eq_zero_of_val_eq_zero_abelian A g L u hA _ _ fun z hz ↦ ?_
    have hz3 := hz
    rw [hinf, hinf, hinf, hinf, hinf] at hz3
    rw [vsub _ _ _ z hz, vadd _ _ _ z hz, hres' _ _ _ _ z hz, hres' _ _ _ _ z hz, hres' _ _ _ _ z hz,
      hf i j z (by rw [hinf, hinf, hinf]; exact ⟨⟨hz3.1.1.1, hz3.1.1.2⟩, hz3.1.2.1, hz3.1.2.2⟩),
      hf j k z (by rw [hinf, hinf, hinf]; exact ⟨⟨hz3.1.2.1, hz3.1.2.2⟩, hz3.2.1, hz3.2.2⟩),
      hf i k z (by rw [hinf, hinf, hinf]; exact ⟨⟨hz3.1.1.1, hz3.1.1.2⟩, hz3.2.1, hz3.2.2⟩)]
    ring
  have hcov' : U.1 ≤ ⨆ i, U.1 ⊓ W i := by
    rw [← inf_iSup_eq, hcov, inf_top_eq]
  obtain ⟨a, ha⟩ := GlobalTheory.T.cechOneCocycle_affineOpen_isCoboundary A.left U.1 U.2 K (fun i ↦ U.1 ⊓ W i) (fun i ↦ inf_le_left) hcov' f hcoc
  have key : ∀ i j z, z ∈ pre u.ex (U.1 ⊓ W i) → z ∈ pre u.ex (U.1 ⊓ W j) →
      h i z - val u.ex _ (a i) z = h j z - val u.ex _ (a j) z := by
    intro i j z hi hj
    have hz : z ∈ pre u.ex ((U.1 ⊓ W i) ⊓ (U.1 ⊓ W j)) := by rw [hinf]; exact ⟨hi, hj⟩
    have h1 := hf i j z hz
    rw [ha i j, vsub _ _ _ z hz, hres' _ _ _ _ z hz, hres' _ _ _ _ z hz] at h1
    linear_combination -h1
  classical
  refine ⟨fun z ↦ if hz : ∃ i, z ∈ pre u.ex (U.1 ⊓ W i) then
      h hz.choose z - val u.ex _ (a hz.choose) z else 0, fun i ↦ ⟨-(a i), fun z hz ↦ ?_⟩⟩
  have hex : ∃ i, z ∈ pre u.ex (U.1 ⊓ W i) := ⟨i, hz⟩
  simp only [Pi.sub_apply, dif_pos hex]
  rw [key _ i z hex.choose_spec hz, vneg _ _ z hz]
  ring

end GlobalTheory.CechPer
end
end

section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem GlobalTheory.PDivLat.latt_free_finrank : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, HasDatum hε G → Module.Free (Ainf p O) (latt G) ∧ Module.Finite (Ainf p O) (latt G) ∧ Module.finrank (Ainf p O) (latt G) = G.height := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G hG
  obtain ⟨D, e, fil, _lie, hal, _⟩ := hG
  obtain ⟨L, -⟩ := GlobalTheory.T.hodgeTate_lattice_eq_rowSpace_of_sandwich_datum p C v O hv ε hε G G.height D e fil hal
  haveI : Nontrivial (PreTilt O p) := CharP.nontrivial_of_char_ne_one (Fact.out : p.Prime).ne_one
  refine ⟨Module.Free.of_equiv L, Module.Finite.equiv L, ?_⟩
  rw [← L.finrank_eq, Module.finrank_fin_fun]
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal

theorem _root_.GlobalTheory.T.exists_latticePoints_integralIdeles_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 c : Ideal (OF E)), IsBaseCond 𝔣 → 𝔣 ∣ c → c ≠ ⊥ → ∃ e : (Σ q : PicO c, modUnits (lattice c q.out)) ≃ {z : (Af E)ˣ ⧸ hatOUnits c // ∃ y : (Af E)ˣ, (QuotientGroup.mk y : (Af E)ˣ ⧸ hatOUnits c) = z ∧ (y : Af E) ∈ hatO c}, ∀ p, ∀ y : (Af E)ˣ, (y : Af E) = algebraMap E (Af E) (p.2.1.out) * (((Quotient.out p.1 : (Af E)ˣ)⁻¹ : (Af E)ˣ) : Af E) → (e p).1 = QuotientGroup.mk y := by
  first | exact @GlobalTheory.CMVal.LatBij.exists_equiv | exact GlobalTheory.CMVal.LatBij.exists_equiv | (intros; apply GlobalTheory.CMVal.LatBij.exists_equiv <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.lie_multiplicities_geometric_points_descend : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp R) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (act : OActN D.O A) (act₀ : OActN D.O A₀), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) (β : R →+* k), x ≫ (π ≫ sY) = spMap β → ∀ i, LieMult (act.toF D) x (β.comp (b.t i)) D.m) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y) (β : R →+* k), x ≫ sY = spMap β → ∀ i, LieMult (act₀.toF D) x (β.comp (b.t i)) D.m) := by
  first | exact @GlobalTheory.LieDesc.lieMult_descend | exact GlobalTheory.LieDesc.lieMult_descend | (intros; apply GlobalTheory.LieDesc.lieMult_descend; all_goals assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.harrisTaylorPullback_comp_factors : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S₀ S₁ T : Scheme.{0}) (s₀ : S₀ ⟶ Sp R) (s₁ : S₁ ⟶ Sp R) (t : T ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s₀) (o₁ : GlobalTheory.UPel.HT.Obj b N s₁) (o : GlobalTheory.UPel.HT.Obj b N t) (g : S₁ ⟶ S₀) (h : T ⟶ S₁), GlobalTheory.UPel.HT.ObjMap o₁ o₀ g → GlobalTheory.UPel.HT.ObjMap o o₀ (h ≫ g) → Nonempty (GlobalTheory.UPel.HT.ObjMap o o₁ h) := by
  first | exact @GlobalTheory.UPel.HT.PullFactor.objMap_factor | exact GlobalTheory.UPel.HT.PullFactor.objMap_factor | (intros; apply GlobalTheory.UPel.HT.PullFactor.objMap_factor <;> assumption)
end
