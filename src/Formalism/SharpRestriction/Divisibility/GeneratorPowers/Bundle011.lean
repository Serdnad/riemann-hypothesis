module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle008
public import Mathlib.Tactic.ENatToNat
public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle018
public import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField TopologicalSpace Opposite MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem isAbelianScheme_of_proper {S : Scheme.{0}} (G : Over S) [GrpObj G] (hs : IsSemiAbelian G)
    (hp : IsProper G.hom) : IsAbelianScheme G := ⟨hs.comm, hs.smooth, hp, hs.geomConnected⟩

theorem isAbelianScheme_univ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) : IsAbelianScheme Xo.univ.t.G := isAbelianScheme_of_proper _ Xo.univ.t.semi Xo.univ.proper

theorem wchart_cover {X Y : Scheme.{0}} (L : LB X) (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) : (⊤ : Y.Opens) ≤ ⨆ j, LB.wchart L φ j := by
  intro y _
  have hk : ∀ k, ∃ i, (φ k).base y ∈ L.U i := fun k => by
    have hy : (φ k).base y ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
    simpa [TopologicalSpace.Opens.mem_iSup] using hy
  choose j hj using hk
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨j, ?_⟩
  show y ∈ ⋂ k, (φ k).base ⁻¹' (L.U (j k) : Set X)
  exact Set.mem_iInter.2 fun k => hj k

theorem gen_ratio {Y : Scheme.{0}} (M : LB Y) (hcov : (⊤ : Y.Opens) ≤ ⨆ j, M.U j)
    (t t' : LB.Gen M) (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ u : Γ(Y, ⊤)ˣ, ∀ j, t.s j = res (le_top : M.U j ≤ ⊤) u * t'.s j := by
  classical
  let r : ∀ j, Γ(Y, M.U j)ˣ := fun j => t.s j / t'.s j
  have hcompat : ∀ i j, res (inf_le_left : M.U i ⊓ M.U j ≤ M.U i) (r i) =
      res (inf_le_right : M.U i ⊓ M.U j ≤ M.U j) (r j) := by
    intro i j
    simp only [r, map_div, ht i j, ht' i j, mul_div_mul_left_eq_div]
  have hcompat' : ∀ i j, res (inf_le_left : M.U i ⊓ M.U j ≤ M.U i) (r i)⁻¹ =
      res (inf_le_right : M.U i ⊓ M.U j ≤ M.U j) (r j)⁻¹ := by
    intro i j
    rw [map_inv, map_inv, hcompat i j]
  obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' M.U ⊤ (fun j => homOfLE le_top) hcov
    (fun j => ((r j : Γ(Y, M.U j)ˣ) : Γ(Y, M.U j))) (fun i j => congrArg Units.val (hcompat i j))
  obtain ⟨b, hb, -⟩ := Y.sheaf.existsUnique_gluing' M.U ⊤ (fun j => homOfLE le_top) hcov
    (fun j => (((r j)⁻¹ : Γ(Y, M.U j)ˣ) : Γ(Y, M.U j))) (fun i j => congrArg Units.val (hcompat' i j))
  have hab : a * b = 1 := by
    refine Y.sheaf.eq_of_locally_eq' M.U ⊤ (fun j => homOfLE le_top) hcov _ _ fun j => ?_
    change (Y.presheaf.map (homOfLE (le_top : M.U j ≤ ⊤)).op).hom (a * b) =
      (Y.presheaf.map (homOfLE (le_top : M.U j ≤ ⊤)).op).hom 1
    erw [map_mul, map_one]
    have e1 := ha j
    have e2 := hb j
    change (Y.presheaf.map (homOfLE (le_top : M.U j ≤ ⊤)).op).hom a = ((r j : Γ(Y, M.U j)ˣ) : Γ(Y, M.U j)) at e1
    change (Y.presheaf.map (homOfLE (le_top : M.U j ≤ ⊤)).op).hom b =
      (((r j)⁻¹ : Γ(Y, M.U j)ˣ) : Γ(Y, M.U j)) at e2
    rw [e1, e2, Units.mul_inv]
  refine ⟨⟨a, b, hab, by erw [mul_comm]; exact hab⟩, fun j => ?_⟩
  have hres : res (le_top : M.U j ≤ ⊤) ⟨a, b, hab, by erw [mul_comm]; exact hab⟩ = r j :=
    Units.ext (ha j)
  rw [hres]
  simp only [r, div_mul_cancel]

private theorem res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V)
    (x : Γ(X, U)ˣ) : res h2 (res h1 x) = res (h2.trans h1) x := by
  apply Units.ext
  change ((X.presheaf.map (homOfLE h1).op ≫ X.presheaf.map (homOfLE h2).op).hom (x : Γ(X, U))) = _
  rw [← Functor.map_comp]
  rfl

theorem pull_res_val {X Y : Scheme.{0}} (h : Y ⟶ X) {V : X.Opens} {W : Y.Opens} (hWV : W ≤ h ⁻¹ᵁ V)
    (u : Γ(X, ⊤)ˣ) :
    ((res hWV (pullU h V (res (le_top : V ≤ ⊤) u)) : Γ(Y, W)ˣ) : Γ(Y, W)) =
      (Y.presheaf.map (homOfLE (le_top : W ≤ h ⁻¹ᵁ ⊤)).op).hom ((h.app ⊤).hom (u : Γ(X, ⊤))) := by
  rw [ReciprocityTheory.ChartRestriction.G.DVR.pullU_res, res_res_lemma]
  rfl

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(X, U)ˣ) :
    res h2 (res h1 x) = res (h2.trans h1) x := by
  exact res_res_lemma h1 h2 x

theorem pull_restrict_unit_value {X Y : Scheme.{0}} (h : Y ⟶ X) {V : X.Opens} {W W' : Y.Opens} (hWV : W ≤ h ⁻¹ᵁ V)
    (hW' : W' ≤ W) (u : Γ(X, ⊤)ˣ) :
    ((res hW' (res hWV (pullU h V (res (le_top : V ≤ ⊤) u))) : Γ(Y, W')ˣ) : Γ(Y, W')) =
      (Y.presheaf.map (homOfLE (le_top : W' ≤ h ⁻¹ᵁ ⊤)).op).hom ((h.app ⊤).hom (u : Γ(X, ⊤))) := by
  rw [res_res, pull_res_val]

theorem unit_sec {S : Scheme.{0}} : ∃ ι : S ⟶ (𝟙_ (Over S)).left, ι ≫ (𝟙_ (Over S)).hom = 𝟙 S := ⟨(CartesianMonoidalCategory.toUnit (Over.mk (𝟙 S))).left, by
  simpa using Over.w (CartesianMonoidalCategory.toUnit (Over.mk (𝟙 S)))⟩

theorem pull_unit_eq_one {X Y S0 : Scheme.{0}} (L : LB X) (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : S0 ⟶ Y) (ψ : S0 ⟶ X)
    (rig : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => ψ) fun _ => 1))
    (t t' : LB.Gen (LB.LinComb L φ ε)) (u : Γ(Y, ⊤)ˣ)
    (hu : ∀ j, t.s j = res (le_top : (LB.LinComb L φ ε).U j ≤ ⊤) u * t'.s j)
    (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε t h) rig)
    (hc' : LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε t' h) rig) :
    (h.app ⊤).hom (u : Γ(Y, ⊤)) = 1 := by
  classical
  have hpt : ∀ (m : S0 ⟶ X) (z : S0), ∃ i, m.base z ∈ L.U i := fun m z => by
    have hz : m.base z ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
    simpa [TopologicalSpace.Opens.mem_iSup] using hz
  let c : S0 → (S0 ⟶ X) → L.ι := fun z m =>
    if m = ψ then (hpt ψ z).choose else (hpt m z).choose
  have hc_mem : ∀ z m, m.base z ∈ L.U (c z m) := by
    intro z m
    simp only [c]
    split_ifs with hm
    · subst hm; exact (hpt _ z).choose_spec
    · exact (hpt m z).choose_spec
  let j : S0 → K → L.ι := fun z k => c z (h ≫ φ k)
  let j' : S0 → PUnit → L.ι := fun z _ => c z ψ
  let W : S0 → S0.Opens := fun z =>
    LB.wchart L (fun k => h ≫ φ k) (j z) ⊓ LB.wchart L (fun _ : PUnit => ψ) (j' z)
  have hzW : ∀ z, z ∈ W z := fun z =>
    ⟨Set.mem_iInter.2 fun k => hc_mem z _, Set.mem_iInter.2 fun _ => hc_mem z ψ⟩
  have hone : ∀ z, (S0.presheaf.map (homOfLE (le_top : W z ≤ h ⁻¹ᵁ ⊤)).op).hom
      ((h.app ⊤).hom (u : Γ(Y, ⊤))) = 1 := by
    intro z
    have hcoh : LB.Coh L (fun k => h ≫ φ k) (j z) := fun k1 k2 e => congrArg (c z) e
    have hcoh' : LB.Coh L (fun _ : PUnit => ψ) (j' z) := fun _ _ _ => rfl
    have hcomp : ∀ k k', (fun k => h ≫ φ k) k = (fun _ : PUnit => ψ) k' → j z k = j' z k' :=
      fun k k' e => congrArg (c z) e
    have e := (hc (j z) (j' z) hcoh hcoh' hcomp).trans (hc' (j z) (j' z) hcoh hcoh' hcomp).symm
    simp only [LB.pullGen] at e
    rw [hu (j z)] at e
    simp only [map_mul] at e
    erw [map_mul] at e
    have e2 := mul_eq_right.mp e
    have e3 := congrArg Units.val e2
    have hWV : LB.wchart L (fun k => h ≫ φ k) (j z) ≤ h ⁻¹ᵁ LB.wchart L φ (j z) :=
      fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
    exact (pull_restrict_unit_value h (W' := W z) hWV inf_le_left u).symm.trans (e3.trans Units.val_one)
  refine S0.sheaf.eq_of_locally_eq' W (h ⁻¹ᵁ ⊤) (fun z => homOfLE le_top) ?_ _ _ ?_
  · intro z _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨z, hzW z⟩
  · intro z
    change (S0.presheaf.map (homOfLE (le_top : W z ≤ h ⁻¹ᵁ ⊤)).op).hom
      ((h.app ⊤).hom (u : Γ(Y, ⊤))) = (S0.presheaf.map (homOfLE (le_top : W z ≤ h ⁻¹ᵁ ⊤)).op).hom 1
    rw [hone z, map_one]

theorem primUniqOfGlobal_holds : PrimUniqOfGlobalSt := by
  intro hglob E _ _ _ H Dw l Xo hab wP wP' hP hP'
  obtain ⟨u, hu⟩ := gen_ratio _ (wchart_cover Xo.univ.t.PP.L Xo.univ.t.PP.isLB _) wP wP' hP.1 hP'.1
  have h1 := pull_unit_eq_one Xo.univ.t.PP.L Xo.univ.t.PP.isLB _ _ (eSec Xo.univ.t.G) (eSec Xo.univ.t.G)
    Xo.univ.t.PP.rig wP wP' u hu hP.2 hP'.2
  have hu1 : u = 1 := by
    obtain ⟨ι, hι⟩ := unit_sec (S := Xo.X)
    obtain ⟨c, hc⟩ := (hglob _ _ hab).2 (u : Γ(Xo.univ.t.G.left, ⊤))
    have e1 : eSec Xo.univ.t.G ≫ Xo.univ.t.G.hom = (𝟙_ (Over Xo.X)).hom := Over.w _
    have hc1 : c = 1 := by
      calc c = (ι ≫ (𝟙_ (Over Xo.X)).hom).appTop.hom c := by rw [hι]; simp
        _ = ι.appTop.hom ((eSec Xo.univ.t.G).appTop.hom (Xo.univ.t.G.hom.appTop.hom c)) := by
            rw [← e1, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]; rfl
        _ = 1 := by
            rw [hc]
            change ι.appTop.hom (((eSec Xo.univ.t.G).app ⊤).hom (u : Γ(Xo.univ.t.G.left, ⊤))) = 1
            rw [h1]
            exact map_one _
    apply Units.ext
    rw [← hc, hc1, map_one, Units.val_one]
  subst hu1
  cases wP
  cases wP'
  congr
  funext j
  simpa using hu j

theorem primUniq_of_global (hglob : GlobalFnsSt) : PrimUniqSt := fun E _ _ _ H Dw l Xo wP wP' hP hP' =>
  primUniqOfGlobal_holds hglob E H Dw l Xo (isAbelianScheme_univ Xo) wP wP' hP hP'

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField Formalism.MainNotions.ModuliIntegralCharts

def PhiCSpanStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E),
    (∀ c : 𝓞 E, ∃ c' : 𝓞 E, (c' : E) = cj c) →
    ∀ (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] (w₀ : 𝓞 E), (w₀ : E) + cj w₀ = 1 →
    ∀ (β : SymB cj Y), (∀ a, 0 ≤ (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) →
    ∀ (k : ℕ) (x : Fin k → Y),
      (∀ y : Y, ∃ n : ℕ, 0 < n ∧ n • y ∈ Submodule.span (𝓞 E) (Set.range x)) →
      phiC cj β ≤ ∑ b, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • x b) (x b)

def PhiCMinimaStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E),
    (∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z)) → (∃ z : E, cj z ≠ z) →
    ∀ (w₀ : 𝓞 E), (w₀ : E) + cj w₀ = 1 →
    ∀ (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
      (β : SymB cj Y),
      (∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ Y),
        (Matrix.of fun i j => (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b i) (b j)).PosDef) →
      ∃ v : Fin (Module.finrank ℤ Y) → Y, LinearIndependent ℤ v ∧
        ∀ i, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (v i) (v i) / 2 ≤
          (|(NumberField.discr E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ E)) /
              (2 * Module.finrank ℚ E) * (Module.finrank ℤ Y : ℝ) ^ 2 * phiC cj β

def PhiCTieStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E) (Y : Type) [AddCommGroup Y]
    [Module (𝓞 E) Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (l : SymB cj Y →ₗ[ℝ] ℝ),
    (∀ β : SymB cj Y, (∀ a c, ∃ z : ℤ, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) → ∃ z : ℤ, l β = z) →
    ∃ (m : ℕ) (x x' : Fin m → Y), ∀ β : SymB cj Y,
      l β = ∑ i, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (x i) (x' i)

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.TB

namespace GaugeR

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

@[reducible] def barStar (H : Host E) : StarRing (𝓞 E) where
  star := H.bar
  star_involutive a := by
    apply RingOfIntegers.ext
    rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]
  star_mul a b := by
    show H.bar (a * b) = H.bar b * H.bar a
    rw [map_mul, mul_comm]
  star_add a b := map_add H.bar a b

variable {H : Host E} {Dw : Datum H} {l : Level H}

def chi (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (σ : E →+* ℂ) : 𝓞 E →+* S :=
  (algebraMap c.F S).comp (embK c σ)

theorem embK_conj (c : Coeff l) (σ : E →+* ℂ) (a : 𝓞 E) :
    embK c (ComplexEmbedding.conjugate σ) a = embK c σ (H.bar a) := by
  apply Subtype.ext
  show (ComplexEmbedding.conjugate σ) (a : E) = σ ((H.bar a : 𝓞 E) : E)
  rw [H.bar_eq, ComplexEmbedding.conjugate_coe_eq, NumberField.IsCMField.complexEmbedding_complexConj]

theorem hunit_chi (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (σ τ : E →+* ℂ) (h : σ ≠ τ) :
    ∃ a, IsUnit (chi c S σ a - chi c S τ a) := by
  classical
  have hex : ∃ a : 𝓞 E, σ (a : E) ≠ τ (a : E) := by
    by_contra hc
    push_neg at hc
    apply h
    ext x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
    rw [map_div₀, map_div₀]
    exact congrArg₂ (· / ·) (hc a) (hc b)
  obtain ⟨a, ha⟩ := hex
  refine ⟨a, ?_⟩
  have hne : embK c σ a - embK c τ a ≠ 0 := by
    intro h0
    apply ha
    exact congrArg (fun z : c.F => (z : ℂ)) (sub_eq_zero.mp h0)
  have hu := (hne.isUnit).map (algebraMap c.F S)
  simpa [chi, map_sub] using hu

def nu (Dw : Datum H) : Lt1 Dw ≃ Fin 1 × Fin (dL Dw) where
  toFun ℓ := ((0 : Fin 1), ltIdx Dw ℓ)
  invFun p := (ltIdx Dw).symm p.2
  left_inv ℓ := by simp
  right_inv p := Prod.ext (Subsingleton.elim _ _) (by simp)

theorem exists_embDomain (x : Fin 1 × Fin (dL Dw) →₀ ℕ) : ∃ y, Finsupp.embDomain (nu Dw).toEmbedding y = x := by
  refine ⟨Finsupp.equivMapDomain (nu Dw).symm x, ?_⟩
  rw [Finsupp.embDomain_eq_mapDomain, Equiv.coe_toEmbedding, ← Finsupp.equivMapDomain_eq_mapDomain]
  ext p
  simp [Finsupp.equivMapDomain_apply]

theorem degree_embDomain {α β : Type} (f : α ↪ β) (y : α →₀ ℕ) : (Finsupp.embDomain f y).degree = y.degree := by
  classical
  show ∑ i ∈ (Finsupp.embDomain f y).support, (Finsupp.embDomain f y) i = ∑ i ∈ y.support, y i
  rw [Finsupp.support_embDomain, Finset.sum_map]
  simp

private theorem coeff_rename_emb_lemma {S : Type} [CommRing S] (p : MvPowerSeries (Lt1 Dw) S)
    (y : Lt1 Dw →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.embDomain (nu Dw).toEmbedding y) (MvPowerSeries.rename (nu Dw).toEmbedding p) =
      MvPowerSeries.coeff y p :=
  MvPowerSeries.coeff_embDomain_rename _ _ _

theorem rename_rescale {S : Type} [CommRing S] (s : Fin 1 × Fin (dL Dw) → S) (p : MvPowerSeries (Lt1 Dw) S) :
    MvPowerSeries.rename (nu Dw).toEmbedding (MvPowerSeries.rescale (fun ℓ => s (nu Dw ℓ)) p) =
      MvPowerSeries.rescale s (MvPowerSeries.rename (nu Dw).toEmbedding p) := by
  ext x
  obtain ⟨y, rfl⟩ := exists_embDomain (Dw := Dw) x
  simp only [coeff_rename_emb_lemma, MvPowerSeries.coeff_rescale, Finsupp.prod_embDomain] <;> rfl

def sc (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (a : 𝓞 E) : Fin 1 × Fin (dL Dw) → S :=
  fun p => algebraMap c.F S (embK c ((ltIdx Dw).symm p.2).1 a)

theorem ratio_exp (hR : GaugeRatioSt) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    (r : MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (h1 : MvPowerSeries.constantCoeff r = 1)
    (hr : ∀ a : 𝓞 E, MvPowerSeries.rescale (sc (Dw := Dw) c S (1 + a * H.bar a)) r =
      MvPowerSeries.rescale (sc (Dw := Dw) c S a) r ^ 2 * r * MvPowerSeries.rescale (sc (Dw := Dw) c S (a * H.bar a)) r) :
    ∃ q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S, MvPowerSeries.constantCoeff q = 0 ∧
      (∀ m, MvPowerSeries.coeff m q ≠ 0 → m.degree = 2) ∧
      (∀ ℓ ℓ' : Lt1 Dw, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ) 1 +
          Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ') 1) q ≠ 0 → ℓ'.1 = ComplexEmbedding.conjugate ℓ.1) ∧
      r = PowerSeries.subst q (PowerSeries.exp S) := by
  letI : StarRing (𝓞 E) := barStar H
  let r' : MvPowerSeries (Lt1 Dw) S := fun y => MvPowerSeries.coeff (Finsupp.embDomain (nu Dw).toEmbedding y) r
  have hcr' : ∀ y, MvPowerSeries.coeff y r' = MvPowerSeries.coeff (Finsupp.embDomain (nu Dw).toEmbedding y) r :=
    fun y => rfl
  have hrr : MvPowerSeries.rename (nu Dw).toEmbedding r' = r := by
    ext x
    obtain ⟨y, rfl⟩ := exists_embDomain (Dw := Dw) x
    rw [coeff_rename_emb_lemma, hcr']
  have hinj : ∀ p p' : MvPowerSeries (Lt1 Dw) S,
      MvPowerSeries.rename (nu Dw).toEmbedding p = MvPowerSeries.rename (nu Dw).toEmbedding p' → p = p' := by
    intro p p' hpp
    ext y
    have hc := congrArg (MvPowerSeries.coeff (Finsupp.embDomain (nu Dw).toEmbedding y)) hpp
    simpa only [coeff_rename_emb_lemma] using hc
  have hsc : ∀ b : 𝓞 E, (fun ℓ : Lt1 Dw => sc (Dw := Dw) c S b (nu Dw ℓ)) = fun ℓ => chi c S ℓ.1 b := by
    intro b
    funext ℓ
    simp [sc, chi, nu]
  have hscale : ∀ (b : 𝓞 E) (p : MvPowerSeries (Lt1 Dw) S),
      MvPowerSeries.rename (nu Dw).toEmbedding (scaleBy (rk := Dw.mult) (chi c S) b p) =
        MvPowerSeries.rescale (sc (Dw := Dw) c S b) (MvPowerSeries.rename (nu Dw).toEmbedding p) := by
    intro b p
    (rw [← rename_rescale, hsc b]) <;> rfl
  have hr0' : MvPowerSeries.constantCoeff r' = 1 := by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hcr', Finsupp.embDomain_zero,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h1]
  have hr' : ∀ a : 𝓞 E, scaleBy (rk := Dw.mult) (chi c S) (1 + a * star a) r' =
      scaleBy (rk := Dw.mult) (chi c S) a r' ^ 2 * r' * scaleBy (rk := Dw.mult) (chi c S) (a * star a) r' := by
    intro a
    apply hinj
    rw [map_mul, map_mul, map_pow, hscale, hscale, hscale, hrr]
    exact hr a
  have hcc : ∀ (σ : E →+* ℂ) (a : 𝓞 E), chi c S (ComplexEmbedding.conjugate σ) a = chi c S σ (star a) := by
    intro σ a
    simp only [chi, RingHom.comp_apply]
    (rw [embK_conj]) <;> rfl
  obtain ⟨q', hq0, hqdeg, hqpair, hqexp⟩ :=
    hR (𝓞 E) S (E →+* ℂ) Dw.mult (chi c S) ComplexEmbedding.conjugate hcc
      (fun σ τ hστ => hunit_chi c S σ τ hστ) r' hr0' hr'
  have hq0r : MvPowerSeries.constantCoeff (MvPowerSeries.rename (nu Dw).toEmbedding q') = 0 := by
    rw [MvPowerSeries.constantCoeff_rename, hq0]
  refine ⟨MvPowerSeries.rename (nu Dw).toEmbedding q', hq0r, ?_, ?_, ?_⟩
  · intro m hm
    obtain ⟨y, rfl⟩ := exists_embDomain (Dw := Dw) m
    rw [coeff_rename_emb_lemma] at hm
    rw [degree_embDomain]
    exact hqdeg y hm
  · intro ℓ ℓ' hm
    have hsum : Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ) 1 + Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ') 1 =
        Finsupp.embDomain (nu Dw).toEmbedding (Finsupp.single ℓ 1 + Finsupp.single ℓ' 1) := by
      (rw [Finsupp.embDomain_add, Finsupp.embDomain_single, Finsupp.embDomain_single]) <;> rfl
    rw [hsum, coeff_rename_emb_lemma] at hm
    exact hqpair ℓ ℓ' hm
  · ext m
    obtain ⟨y, rfl⟩ := exists_embDomain (Dw := Dw) m
    rw [← hrr, coeff_rename_emb_lemma, hqexp,
      PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hq0),
      PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hq0r)]
    congr 1
    funext d
    rw [← map_pow, coeff_rename_emb_lemma]

end GaugeR

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end
