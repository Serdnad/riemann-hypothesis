module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2736
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2751
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2755
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2982
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle044
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2946
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2976
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSmoothGroupOverNbhd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendsToSemiAbelianOfLocalGroups
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2947
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.ringKrullDim_le_of_isEtaleCompletion : ∀ (O A : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (ψ : O →+* A) [IsLocalHom ψ], IsEtaleCompletion ψ → ringKrullDim A ≤ ringKrullDim O := by
  intro O A _ _ _ _ _ _ ψ _ h
  letI : Algebra O A := ψ.toAlgebra
  have hmap : (maximalIdeal O).map (algebraMap O A) = maximalIdeal A := h.2.1
  have hlo : (maximalIdeal A).LiesOver (maximalIdeal O) := by
    refine ⟨?_⟩
    rw [Ideal.under_def]
    exact (IsLocalRing.maximalIdeal_comap ψ).symm
  have key := Ideal.height_le_height_add_of_liesOver (maximalIdeal O) (maximalIdeal A)
  rw [hmap, Ideal.map_quotient_self] at key
  have h0 : (⊥ : Ideal (A ⧸ maximalIdeal A)).height = 0 := by
    simp
  rw [h0, add_zero] at key
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  exact_mod_cast key
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtUniq

theorem sub_mem_pow_of_mem_maximalIdeal {O W V : Type} [CommRing O] [IsLocalRing O] [CommRing W]
    [IsLocalRing W] [CommRing V] [IsLocalRing V] (φ : O →+* W)
    (hm : (maximalIdeal O).map φ = maximalIdeal W)
    (θ₁ θ₂ : W →+* V) [IsLocalHom θ₂] (hO : θ₁.comp φ = θ₂.comp φ) (k : ℕ)
    (hk : ∀ w, θ₁ w - θ₂ w ∈ maximalIdeal V ^ (k + 1)) :
    ∀ x ∈ maximalIdeal W, θ₁ x - θ₂ x ∈ maximalIdeal V ^ (k + 2) := by
  intro x hx
  rw [← hm] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, -, rfl⟩ := hy
    have := congrArg (fun f => f a) hO
    simp only [RingHom.comp_apply] at this
    rw [this, sub_self]; exact zero_mem _
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _), map_add (f := _), add_sub_add_comm]; exact add_mem hx hy
  | smul a x hx' hx =>
    have hx'' : x ∈ maximalIdeal W := by rw [← hm]; exact hx'
    have h2 : θ₂ x ∈ maximalIdeal V :=
      (mem_maximalIdeal _).2 fun h => (mem_maximalIdeal _).1 hx'' (isUnit_of_map_unit θ₂ x h)
    simp only [smul_eq_mul, map_mul]
    have e : θ₁ a * θ₁ x - θ₂ a * θ₂ x = θ₁ a * (θ₁ x - θ₂ x) + (θ₁ a - θ₂ a) * θ₂ x := by ring
    rw [e]
    refine add_mem (Ideal.mul_mem_left _ _ hx) ?_
    rw [show k + 2 = (k + 1) + 1 from rfl, pow_succ]
    exact Ideal.mul_mem_mul (hk a) h2

abbrev Gr (V : Type) [CommRing V] [IsLocalRing V] (k : ℕ) : Type :=
  ↥(maximalIdeal V ^ (k + 1)) ⧸ (maximalIdeal V • (⊤ : Submodule V ↥(maximalIdeal V ^ (k + 1))))

noncomputable instance (V : Type) [CommRing V] [IsLocalRing V] (k : ℕ) : Module (ResidueField V) (Gr V k) :=
  inferInstanceAs (Module (V ⧸ maximalIdeal V) (Gr V k))

noncomputable abbrev grModule {W V : Type} [CommRing W] [IsLocalRing W] [CommRing V] [IsLocalRing V]
    (θ : W →+* V) [IsLocalHom θ] (k : ℕ) : Module (ResidueField W) (Gr V k) :=
  Module.compHom _ (ResidueField.map θ)

theorem gr_mk_eq_zero_iff (V : Type) [CommRing V] [IsLocalRing V] (k : ℕ)
    (v : ↥(maximalIdeal V ^ (k + 1))) :
    (Submodule.Quotient.mk v : Gr V k) = 0 ↔ (v : V) ∈ maximalIdeal V ^ (k + 2) := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_top_iff, Ideal.smul_eq_mul, ← pow_succ']

theorem gr_mk_eq_mk (V : Type) [CommRing V] [IsLocalRing V] (k : ℕ)
    (u v : ↥(maximalIdeal V ^ (k + 1))) (h : (u : V) - v ∈ maximalIdeal V ^ (k + 2)) :
    (Submodule.Quotient.mk u : Gr V k) = Submodule.Quotient.mk v := by
  rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, gr_mk_eq_zero_iff]; simpa using h

theorem sub_mem_pow_succ {O W V : Type} [CommRing O] [IsLocalRing O] [CommRing W]
    [IsLocalRing W] [CommRing V] [IsLocalRing V] (φ : O →+* W)
    (hm : (maximalIdeal O).map φ = maximalIdeal W)
    (hu : ((residue W).comp φ).FormallyUnramified)
    (θ₁ θ₂ : W →+* V) [IsLocalHom θ₁] [IsLocalHom θ₂] (hO : θ₁.comp φ = θ₂.comp φ) (k : ℕ)
    (hk : ∀ w, θ₁ w - θ₂ w ∈ maximalIdeal V ^ (k + 1)) :
    ∀ w, θ₁ w - θ₂ w ∈ maximalIdeal V ^ (k + 2) := by
  have hW := sub_mem_pow_of_mem_maximalIdeal φ hm θ₁ θ₂ hO k hk
  letI : Algebra O (ResidueField W) := ((residue W).comp φ).toAlgebra
  haveI : Algebra.FormallyUnramified O (ResidueField W) := hu
  letI : Module (ResidueField W) (Gr V k) := grModule θ₁ k
  letI : Module O (Gr V k) := Module.compHom _ (algebraMap O (ResidueField W))
  haveI : IsScalarTower O (ResidueField W) (Gr V k) := ⟨fun a b x => by
    show ResidueField.map θ₁ (a • b) • x = ResidueField.map θ₁ (algebraMap O _ a) • (ResidueField.map θ₁ b • x)
    rw [Algebra.smul_def, map_mul, mul_smul]⟩
  let δ₀ : W → Gr V k := fun w => Submodule.Quotient.mk ⟨θ₁ w - θ₂ w, hk w⟩
  have hsm : ∀ (c : W) (v : ↥(maximalIdeal V ^ (k + 1))), residue W c • (Submodule.Quotient.mk v : Gr V k) =
      Submodule.Quotient.mk (θ₁ c • v) := by
    intro c v
    show ResidueField.map θ₁ (residue W c) • (Submodule.Quotient.mk v : Gr V k) = _
    rw [ResidueField.map_residue]
    rfl
  let s := Function.surjInv (residue_surjective (R := W))
  have hs : ∀ w, δ₀ (s (residue W w)) = δ₀ w := by
    intro w
    refine gr_mk_eq_mk V k _ _ ?_
    have hmem : s (residue W w) - w ∈ maximalIdeal W := by
      rw [← Ideal.Quotient.eq]
      exact Function.surjInv_eq _ _
    have := hW _ hmem
    simp only [map_sub] at this ⊢
    convert this using 1; ring
  let D : Derivation O (ResidueField W) (Gr V k) :=
    { toFun := fun x => δ₀ (s x)
      map_add' := by
        intro x y
        obtain ⟨a, rfl⟩ := residue_surjective x
        obtain ⟨b, rfl⟩ := residue_surjective y
        rw [← map_add (f := _), hs, hs, hs, ← Submodule.Quotient.mk_add]
        refine gr_mk_eq_mk V k _ _ ?_
        simp only [Submodule.coe_add, map_add (f := _)]
        convert zero_mem (maximalIdeal V ^ (k + 2)) using 1; ring
      map_smul' := by
        intro c x
        obtain ⟨a, rfl⟩ := residue_surjective x
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def, show algebraMap O (ResidueField W) c = residue W (φ c) from rfl,
          ← map_mul, hs, hs]
        show _ = residue W (φ c) • δ₀ a
        rw [hsm]
        refine gr_mk_eq_mk V k _ _ ?_
        simp only [Submodule.coe_smul, smul_eq_mul, map_mul]
        have := congrArg (fun f => f c) hO
        simp only [RingHom.comp_apply] at this
        rw [this]
        convert zero_mem (maximalIdeal V ^ (k + 2)) using 1; ring
      map_one_eq_zero' := by
        show δ₀ (s 1) = 0
        rw [← map_one (residue W), hs]
        show (Submodule.Quotient.mk _ : Gr V k) = 0
        rw [gr_mk_eq_zero_iff]; simp
      leibniz' := by
        intro x y
        obtain ⟨a, rfl⟩ := residue_surjective x
        obtain ⟨b, rfl⟩ := residue_surjective y
        show δ₀ (s _) = residue W a • δ₀ (s _) + residue W b • δ₀ (s _)
        rw [← map_mul, hs, hs, hs, hsm, hsm, ← Submodule.Quotient.mk_add]
        refine gr_mk_eq_mk V k _ _ ?_
        simp only [Submodule.coe_add, Submodule.coe_smul, smul_eq_mul, map_mul]
        have e : θ₁ a * θ₁ b - θ₂ a * θ₂ b - (θ₁ a * (θ₁ b - θ₂ b) + θ₁ b * (θ₁ a - θ₂ a)) =
            (θ₁ a - θ₂ a) * (θ₂ b - θ₁ b) := by ring
        rw [e, show k + 2 = (k + 1) + 1 from rfl, pow_succ]
        refine Ideal.mul_mem_mul (hk a) ?_
        have := Ideal.pow_le_self (n := k + 1) (I := maximalIdeal V) (by omega) (hk b)
        rw [← neg_sub]; exact neg_mem this }
  have hD : ∀ x, D x = 0 := by
    intro x
    rw [← Derivation.liftKaehlerDifferential_comp_D D x,
      Subsingleton.elim (KaehlerDifferential.D O (ResidueField W) x) 0, map_zero]
  intro w
  have h1 : δ₀ w = 0 := by
    rw [← hs]
    exact hD (residue W w)
  exact (gr_mk_eq_zero_iff V k _).1 h1

theorem localHom_ext : ∀ (O W V : Type) [CommRing O] [IsLocalRing O] [CommRing W] [IsLocalRing W] [IsNoetherianRing W] [CommRing V] [IsLocalRing V] [IsNoetherianRing V] (φ : O →+* W), IsAdicComplete (maximalIdeal W) W → IsEtaleCompletion φ → ((residue W).comp φ).FormallyUnramified → ∀ θ₁ θ₂ : W →+* V, IsLocalHom θ₁ → IsLocalHom θ₂ → θ₁.comp φ = θ₂.comp φ → (∀ w, θ₁ w - θ₂ w ∈ maximalIdeal V) → θ₁ = θ₂ := by
  intro O W V _ _ _ _ _ _ _ _ φ _ hφ hu θ₁ θ₂ h₁ h₂ hO hres
  have hk : ∀ k w, θ₁ w - θ₂ w ∈ maximalIdeal V ^ (k + 1) := by
    intro k
    induction k with
    | zero => simpa using hres
    | succ k ih => exact sub_mem_pow_succ φ hφ.2.1 hu θ₁ θ₂ hO k ih
  ext w
  rw [← sub_eq_zero, ← Ideal.mem_bot,
    ← Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal V).ne_top, Ideal.mem_iInf]
  intro i
  cases i with
  | zero => simp
  | succ i => exact hk i w

end GlobalTheory.EtUniq
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.BalProj

theorem balanced_finite_projective_rank : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → Module.Finite Γ(Y.X, U.1) (balanced H.bar A) ∧ Module.Projective Γ(Y.X, U.1) (balanced H.bar A) ∧ ∀ m : Ideal Γ(Y.X, U.1), m.IsMaximal → Module.finrank (Γ(Y.X, U.1) ⧸ m) ((Γ(Y.X, U.1) ⧸ m) ⊗[Γ(Y.X, U.1)] (balanced H.bar A)) = Dw.dim := by
  intro E _ _ _ H Dw l Xo c Y h1 hsm hsnc U n v A hv hb hA
  obtain ⟨h1A, haddA, hmulA⟩ := GlobalTheory.T.tangentBasis_actionMatrices_ringHom H Y.t Γ(Y.X, U.1) (chart U) n v A hv hb hA
  obtain ⟨hfin, hproj, hrk⟩ := GlobalTheory.T.balancedSymmetricLieTensors_finite_projective_rank H c.F c.conj Γ(Y.X, U.1) (GlobalTheory.BalProj.fnHom Y.s U.1) n A h1A haddA hmulA
  refine ⟨hfin, hproj, fun m hm => ?_⟩
  have key : ∀ τ : E →+* ℂ, GlobalTheory.BalProj.eigRank (algebraMap Γ(Y.X, U.1) m.ResidueField) A
      (GlobalTheory.BalProj.embR c.F c.conj (GlobalTheory.BalProj.fnHom Y.s U.1) τ) = if τ (H.rt : E) = H.rt0 then Dw.p else Dw.q := by
    intro τ
    set e : ℕ := if τ (H.rt : E) = H.rt0 then Dw.p else Dw.q with he
    let f : PrimeSpectrum Γ(Y.X, U.1) → ℕ := fun 𝔭 => GlobalTheory.BalProj.eigRank (algebraMap Γ(Y.X, U.1) 𝔭.asIdeal.ResidueField) A
      (GlobalTheory.BalProj.embR c.F c.conj (GlobalTheory.BalProj.fnHom Y.s U.1) τ)
    have hop : ∀ N, IsOpen {𝔭 | f 𝔭 = N} := fun N =>
      GlobalTheory.T.isOpen_eigenRank_levelSet_integersAction c.F c.conj Γ(Y.X, U.1) (GlobalTheory.BalProj.fnHom Y.s U.1) n A h1A haddA hmulA τ N
    have hcl : IsClosed {𝔭 | f 𝔭 = e} := by
      rw [← isOpen_compl_iff]
      have : {𝔭 | f 𝔭 = e}ᶜ = ⋃ N ∈ {N : ℕ | N ≠ e}, {𝔭 | f 𝔭 = N} := by
        ext 𝔭; simp
      rw [this]
      exact isOpen_biUnion fun N _ => hop N
    have hsub : (chart U).base ⁻¹' (interior Y : Set Y.X) ⊆ {𝔭 | f 𝔭 = e} := fun 𝔭 h𝔭 =>
      GlobalTheory.T.eigenRank_interior_eq_signature E H Dw l Xo c Y h1 hsm hsnc U n v A hv hb hA 𝔭 h𝔭 τ
    have hall : {𝔭 | f 𝔭 = e} = Set.univ :=
      Set.eq_univ_of_univ_subset ((GlobalTheory.T.dense_affineChart_preimage_interior E H Dw l Xo c Y U).closure_eq ▸ (closure_mono hsub).trans hcl.closure_subset)
    have := hall ▸ Set.mem_univ (⟨m, hm.isPrime⟩ : PrimeSpectrum Γ(Y.X, U.1))
    exact this
  have h2 := hrk m
  simp_rw [key] at h2
  rw [GlobalTheory.T.cmType_signature_sum_eq_twice_dimension E H Dw.p Dw.q] at h2
  unfold Datum.dim
  omega

end GlobalTheory.BalProj
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartKSUniq

theorem isKS_unique_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (v i)) → (∀ w, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) w → ∃! cf : Fin n → Γ(Sp (ChartRing k m d), ⊤), IsCombAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) v cf w) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (Θ Θ' : Matrix (Fin n) (Fin n) Γ(Sp (ChartRing k m d), ⊤)), IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) Θ → IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) Θ' → Θ = Θ' := by
  intro E _ _ _ H k _ _ m d t P gam _ _ _ n v hv hb D Θ Θ' h h'
  haveI : CharZero (ChartRing k m d) :=
    charZero_of_injective_algebraMap (R := k) (MvPowerSeries.C_injective (σ := Fin m ⊕ Fin d) (R := k))
  haveI : CharZero (FractionRing (ChartRing k m d)) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective (ChartRing k m d) (FractionRing (ChartRing k m d)))
  let φ : Γ(Sp (ChartRing k m d), ⊤) →+* FractionRing (ChartRing k m d) :=
    (algebraMap (ChartRing k m d) (FractionRing (ChartRing k m d))).comp
      (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom
  have hφ : Function.Injective φ := by
    exact (IsFractionRing.injective (ChartRing k m d) (FractionRing (ChartRing k m d))).comp
      (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).commRingCatIsoToRingEquiv.injective
  have hx : spMap φ ≫ chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) = jK (ChartRing k m d) := by
    show spMap φ ≫ (isAffineOpen_top (Sp (ChartRing k m d))).fromSpec = _
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
    unfold spMap
    rw [← Spec.map_comp]
    congr 1
    ext r
    simp [φ]
  set R := ChartRing k m d with hRdef
  have gpG : IsGrpPullback P.A.A t.G (jK R) (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) :=
    GlobalTheory.ThetaBaseChange.grp_generic P.U.toUnifPre
  have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hext : LBIso (P.A.L.pull P.U.gen.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK R))) := by
    have h := P.U.ext
    rw [P.bundle] at h
    exact h
  have hL : LBIso P.A.L (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R))) := by
    have h1 : LBIso (P.A.L.pull (P.U.gen.inv.left ≫ P.U.gen.hom.left))
        (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R))) :=
      LBIso.chartPull (chartPullSame P.A.L _ (fun _ => P.U.gen.hom.left) _ P.U.gen.inv.left fun _ => rfl)
        (chartPullSame t.PP.L _ (fun _ => pullback.fst t.G.hom (jK R)) _ P.U.gen.inv.left fun _ => rfl) hext
    exact LBIso.chartPull (chartPullUnpull P.A.L _ hgi)
      (chartPullSame t.PP.L _ _ _ (𝟙 _) fun _ => (Category.id_comp _).symm) h1
  have hf : (∏ i, bdParam k m d i : R) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ h0 => by
      have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i : Fin m ⊕ Fin d) 1)) h0
      simp [bdParam, MvPowerSeries.coeff_X] at this
  have hV : ⊤ ≤ (spMap φ ≫ chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ⁻¹ᵁ
      (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, bdParam k m d i)) := by
    intro p _
    change (spMap φ) p ∈ (isAffineOpen_top (Sp R)).fromSpec ⁻¹ᵁ (Sp R).basicOpen _
    rw [(isAffineOpen_top (Sp R)).fromSpec_preimage_basicOpen]
    show PrimeSpectrum.comap φ p ∈ PrimeSpectrum.basicOpen _
    rw [PrimeSpectrum.mem_basicOpen]
    show _ ∉ Ideal.comap φ p.asIdeal
    haveI := p.isPrime
    rw [Ideal.mem_comap, Ideal.eq_bot_of_prime p.asIdeal, Ideal.mem_bot]
    intro h0
    apply hf
    apply IsFractionRing.injective R (FractionRing R)
    rw [map_zero, ← h0]
    show _ = algebraMap R (FractionRing R) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom _))
    rw [Iso.inv_hom_id_apply]
  have key := GlobalTheory.T.kodairaSpencer_unique_at_polarized_fieldPoint E H (Sp R) t _ (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) n v hv hb
    (FractionRing R) φ P.A _ hV (by rw [hx]; exact gpG) hL _ Θ Θ' h h'
  ext a b
  exact hφ (congrFun₂ key a b)

end GlobalTheory.ChartKSUniq
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.squareDecomposition_descends_to_finiteExtension : ∀ (k Ω : Type) [Field k] [Field Ω] (σ : k →+* Ω) (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ (L M : LB A₀.left), L.IsLB → M.IsLB → SqDec ((Over.pullback (spMap σ)).obj A₀) (L.pull (pullback.fst A₀.hom (spMap σ))) (M.pull (pullback.fst A₀.hom (spMap σ))) → ∃ (k₁ : Type) (_ : Field k₁) (_ : Algebra k k₁) (_ : FiniteDimensional k k₁), SqDec ((Over.pullback (spMap (algebraMap k k₁))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k k₁)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k k₁)))) := by
  first | exact @GlobalTheory.SqDecFinite.main | exact GlobalTheory.SqDecFinite.main | (intros; apply GlobalTheory.SqDecFinite.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.baseChange_sends_closedFibre_genericPoint_dvr : ∀ (T D : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] (a : T →+* D), a.Flat → (maximalIdeal T).map a = maximalIdeal D → ∀ (H : Over (Sp T)) [GrpObj H] [IsIntegral H.left] (H' : Over (Sp D)) [GrpObj H'] [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsSemiAbelian H → IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → ∀ (y : H.left) (y' : H'.left), H.hom y = closedPoint T → H'.hom y' = closedPoint D → ringKrullDim (H.left.presheaf.stalk y) = 1 → ringKrullDim (H'.left.presheaf.stalk y') = 1 → π y' = y := by
  first | exact @GlobalTheory.Desc.GaussBC.apply_eq_of_closedFibre_dim_one | exact GlobalTheory.Desc.GaussBC.apply_eq_of_closedFibre_dim_one | (intros; apply GlobalTheory.Desc.GaussBC.apply_eq_of_closedFibre_dim_one <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.cartierSections_flat_baseChange_linearlyDisjoint : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ : R →+* R₁), ρ.Flat → ∀ (X Y V : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp R) (q : Y ⟶ Sp R₁) (i : V ⟶ Y) [IsOpenImmersion i] (φ : V ⟶ X) (θ : X.functionField →+* Y.functionField), QuasiCompact p → QuasiSeparated p → IsPullback φ (i ≫ q) p (spMap ρ) → PFF i φ θ → ∀ (D : CartierDiv X) (D₁ : CartierDiv Y), PPull i φ θ D D₁ → LinDisj (GlobalTheory.Desc.cst p) (GlobalTheory.Desc.cst q) θ ∧ ∀ k : ℕ, {v | ∀ z : V, (k • D₁).RegularAt (i z) v} = spanBy (GlobalTheory.Desc.cst q) (θ '' Sec D k) := by
  first | exact @GlobalTheory.SecFlatBC.sections_linDisj_flatBaseChange | exact GlobalTheory.SecFlatBC.sections_linDisj_flatBaseChange | (intros; apply GlobalTheory.SecFlatBC.sections_linDisj_flatBaseChange <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.proj_model_baseChange_standard_open_app_surjective : ∀ (R F : Type) [CommRing R] [IsDomain R] [Field F] (c₀ : R →+* F) (N : ℕ → Set F), GradedFam c₀ N → ∀ (P : Scheme.{0}) [IsIntegral P] (p : P ⟶ Sp R) (ψ : P.functionField →+* F) (Dp : ℕ → F → P.Opens), IsModel c₀ N p ψ Dp → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (ρ : R →+* R₁), ρ.Flat → Function.Injective c₀ → ∀ (Y : Scheme.{0}) [IsIntegral Y] [CompactSpace Y] [QuasiSeparatedSpace Y] (q : Y ⟶ Sp R₁) (θ : F →+* Y.functionField) (D₁ : CartierDiv Y), θ.comp c₀ = (GlobalTheory.Desc.cst q).comp ρ → LinDisj c₀ (GlobalTheory.Desc.cst q) θ → AmpleDiv D₁ → (∀ k, Sec D₁ k = spanBy (GlobalTheory.Desc.cst q) (θ '' N k)) → ∀ m : Y ⟶ P, PFF (𝟙 _) m (θ.comp ψ) → (∀ k, 1 ≤ k → ∀ b ∈ N k, ∀ y, m y ∈ Dp k b ↔ y ∈ locus D₁ k (θ b)) → ∀ (hm : m ≫ p = q ≫ spMap ρ) (k : ℕ), 1 ≤ k → ∀ b ∈ N k, Function.Surjective ((pullback.lift m q hm).app ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b)) := by
  first | exact @GlobalTheory.Desc.lift_app_surjective | exact GlobalTheory.Desc.lift_app_surjective | (intros; apply GlobalTheory.Desc.lift_app_surjective <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.nonempty_semiAbelianCompletionChart_of_openPart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) {S : Scheme.{0}} (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (A : Over (Xo.XF c)) [GrpObj A], IsSemiAbelian A → ∀ x ∈ Set.range j, Nonempty (GlobalTheory.Desc.Chart j A x) := by
  first | exact @GlobalTheory.Desc.OpenChart.nonempty_chart | exact GlobalTheory.Desc.OpenChart.nonempty_chart | (intros; apply GlobalTheory.Desc.OpenChart.nonempty_chart <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.exists_local_smooth_group_over_nbhd : ∀ (σ : Setup) (E : Emb σ), σ.Common → ∀ x : Sp σ.R, ∃ g : σ.R, g ∉ x.asIdeal ∧ ∃ (H : Over (Sp (Localization.Away g))) (_ : GrpObj H) (h : H.left ⟶ E.P), E.LocGrp g H h ∧ ∀ z : E.P, z ∈ E.U → x.asIdeal ≤ (E.p z).asIdeal → (E.p z).asIdeal ≤ x.asIdeal → z ∈ Set.range h := by
  first | exact @GlobalTheory.Desc.Emb.exists_locGrp | exact GlobalTheory.Desc.Emb.exists_locGrp | (intros; apply GlobalTheory.Desc.Emb.exists_locGrp <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.extendsToSemiAbelian_of_local_groups : ∀ (σ : Setup) (E : Emb σ), σ.Common → (∀ x : Sp σ.R, ∃ g : σ.R, g ∉ x.asIdeal ∧ ∃ (H : Over (Sp (Localization.Away g))) (_ : GrpObj H) (h : H.left ⟶ E.P), E.LocGrp g H h ∧ Set.range h = E.U ∩ E.p ⁻¹' {z : Sp σ.R | g ∉ z.asIdeal}) → HasExt (awayMap σ.f) σ.A := by
  first | exact @GlobalTheory.Desc.Emb.hasExt_of_locGrp | exact GlobalTheory.Desc.Emb.hasExt_of_locGrp | (intros; apply GlobalTheory.Desc.Emb.hasExt_of_locGrp <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_cubicalSymmetricStructure_of_genericSymmetric : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R], ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → IsProper (pullback.snd G.hom (jK R)) → ∀ L : LB G.left, L.IsLB → Out.Sym ((Over.pullback (jK R)).obj G) (L.pull (pullback.fst G.hom (jK R))) → ∃ P : GlobalTheory.UU.CP G, P.L.L = L := by
  first | exact @GlobalTheory.CubSymPkg.exists_cp_of_generic_sym | exact GlobalTheory.CubSymPkg.exists_cp_of_generic_sym | (intros; apply GlobalTheory.CubSymPkg.exists_cp_of_generic_sym <;> assumption)
end
