module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsChartOfMemRedKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2943
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2653
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2745
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2815
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2940
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudTorusWeightZeroInvariantFieldCoeffs
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSymmOfKsCoc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle084
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle089
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle157
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteConesSiegelLevelStructure
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2910
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2311
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2116
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPullbackExistsUnique
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2945
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.TangentOrigin

noncomputable section

namespace GlobalTheory.GcDual

def cHom {K : Type} [Field K] {X : Scheme.{0}} (p : X ⟶ Sp K) (W : X.Opens) : K →+* Γ(X, W) :=
  (p.appLE ⊤ W (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

theorem coeffs_zero {K : Type} [Field K] (P₀ : Out.PolAV (Sp K)) (n : ℕ)
    (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left)
    (hd : ∀ a, IsInv P₀.A (v a) (dd a)) (W : P₀.A.left.Opens) (hW : IsAffineOpen W)
    {C : Type} [CommRing C] (ψ : Γ(P₀.A.left, W) →+* C) (c : Fin n → C)
    (hc : ∀ f, ∑ a, c a * ψ (dd a W f) = 0) : c = 0 := by
  haveI := P₀.smoothDim
  haveI : Smooth P₀.A.hom := SmoothOfRelativeDimension.smooth P₀.g _
  letI : Algebra K C := (ψ.comp (cHom P₀.A.hom W)).toAlgebra
  obtain ⟨x, hx, ex⟩ := exists_evalPt_eq hW ψ
  have hxp : x ≫ P₀.A.hom = (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := K) C).hom := by
    refine (eq_spMap_of_evalPt _ (algebraMap K C) fun a => ?_).trans rfl
    rw [← evalPt_constFn P₀.A.hom x W hx, ex]
    rfl
  let y : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := K) C ⟶ P₀.A := Over.homMk x hxp
  obtain ⟨c₀, -, hu⟩ := GlobalTheory.VertCoeffRing.existsUnique_coeff_alg (GlobalTheory.VertCoeffRing.isLieBasis_tvE v)
    (fun B _ _ e he z O h => GlobalTheory.VertCoeffRing.evalPt_lieExp v dd hd B e he z O h) y hW hx (fun _ => 0)
    (fun _ _ => by simp) (fun _ _ => by simp) (fun _ => rfl)
  have h1 := hu c (fun f => by simpa [y, ex] using (hc f).symm)
  have h2 := hu 0 (fun f => by simp)
  rw [h1, h2]

end GlobalTheory.GcDual

namespace GlobalTheory.GcDual

variable {A : Type} [CommRing A] {n : ℕ}

theorem mem_smul_top_of_forall_mem (I : Ideal A) (x : Fin n → A) (hx : ∀ b, x b ∈ I) :
    x ∈ I • (⊤ : Submodule A (Fin n → A)) := by
  rw [← Finset.univ_sum_single x]
  refine Submodule.sum_mem _ fun b _ => ?_
  have : Pi.single b (x b) = x b • (Pi.single b 1 : Fin n → A) := by
    rw [← Pi.single_smul, smul_eq_mul, _root_.mul_one]
  rw [this]
  exact Submodule.smul_mem_smul (hx b) trivial

theorem eq_top_of_forall_maximal (M : Submodule A (Fin n → A))
    (h : ∀ m : Ideal A, m.IsMaximal → ∀ x, x ∈ M ⊔ m • (⊤ : Submodule A (Fin n → A))) : M = ⊤ := by
  have hQ : ∀ m : Ideal A, m.IsMaximal → ∃ r : A, r - 1 ∈ m ∧ ∀ q : (Fin n → A) ⧸ M, r • q = 0 := by
    intro m hm
    have hle : (⊤ : Submodule A ((Fin n → A) ⧸ M)) ≤ m • ⊤ := by
      intro q _
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective M q
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (h m hm x)
      have hz' : M.mkQ z ∈ m • (⊤ : Submodule A ((Fin n → A) ⧸ M)) := by
        have : m • (⊤ : Submodule A (Fin n → A)) ≤ (m • (⊤ : Submodule A ((Fin n → A) ⧸ M))).comap M.mkQ :=
          Submodule.smul_le.2 fun r hr t _ => by
            rw [Submodule.mem_comap, map_smul]
            exact Submodule.smul_mem_smul hr trivial
        exact this hz
      have e : Submodule.Quotient.mk (p := M) (y + z) = M.mkQ z := by
        rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero M).2 hy, zero_add]; rfl
      rw [e]; exact hz'
    obtain ⟨r, hr, hr'⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m ⊤
      (Module.Finite.fg_top) hle
    exact ⟨r, hr, fun q => hr' q trivial⟩
  have h1 : ∀ q : (Fin n → A) ⧸ M, q = 0 := by
    by_contra hne
    push_neg at hne
    obtain ⟨q₀, hq₀⟩ := hne
    let I : Ideal A := Module.annihilator A ((Fin n → A) ⧸ M)
    have hI : I ≠ ⊤ := by
      intro hI
      have : (1 : A) ∈ I := hI ▸ Submodule.mem_top
      exact hq₀ (by simpa using Module.mem_annihilator.1 this q₀)
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
    obtain ⟨r, hr, hr'⟩ := hQ m hm
    have hrI : r ∈ I := Module.mem_annihilator.2 hr'
    have : (1 : A) ∈ m := by
      have := m.sub_mem (hIm hrI) hr
      simpa using this
    exact hm.ne_top ((Ideal.eq_top_iff_one m).2 this)
  rw [eq_top_iff]
  intro x _
  exact (Submodule.Quotient.mk_eq_zero M).1 (h1 _)

end GlobalTheory.GcDual

namespace GlobalTheory.GcDual

theorem span_eq_top {K : Type} [Field K] (P₀ : Out.PolAV (Sp K)) (n : ℕ)
    (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left)
    (hd : ∀ a, IsInv P₀.A (v a) (dd a)) (W : P₀.A.left.Opens) (hW : IsAffineOpen W) :
    Submodule.span Γ(P₀.A.left, W) (Set.range fun f : Γ(P₀.A.left, W) => fun b => dd b W f) = ⊤ := by
  set M := Submodule.span Γ(P₀.A.left, W) (Set.range fun f : Γ(P₀.A.left, W) => fun b => dd b W f) with hM
  refine eq_top_of_forall_maximal M fun m hm x => ?_
  haveI := hm
  letI : Field (Γ(P₀.A.left, W) ⧸ m) := Ideal.Quotient.field m
  let π : Γ(P₀.A.left, W) →+* Γ(P₀.A.left, W) ⧸ m := Ideal.Quotient.mk m
  let S : Submodule (Γ(P₀.A.left, W) ⧸ m) (Fin n → Γ(P₀.A.left, W) ⧸ m) :=
    Submodule.span _ (Set.range fun f : Γ(P₀.A.left, W) => fun b => π (dd b W f))
  have hS : S = ⊤ := by
    by_contra hS
    obtain ⟨φ, hφ0, hφ⟩ := S.exists_le_ker_of_lt_top (lt_top_iff_ne_top.2 hS)
    classical
    let c : Fin n → Γ(P₀.A.left, W) ⧸ m := fun b => φ fun j => if b = j then 1 else 0
    have hc := coeffs_zero P₀ n v dd hd W hW π c fun f => by
      have := hφ (Submodule.subset_span ⟨f, rfl⟩)
      rw [LinearMap.mem_ker, LinearMap.pi_apply_eq_sum_univ] at this
      simpa [c, smul_eq_mul, mul_comm] using this
    apply hφ0
    refine LinearMap.ext fun z => ?_
    rw [LinearMap.pi_apply_eq_sum_univ]
    have : ∀ i, φ (fun j => if i = j then 1 else 0) = 0 := fun i => congrFun hc i
    simp [this]
  have lift : ∀ y ∈ S, ∃ x₀ ∈ M, (fun b => π (x₀ b)) = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, rfl⟩ := hy
      exact ⟨fun b => dd b W f, Submodule.subset_span ⟨f, rfl⟩, rfl⟩
    | zero => exact ⟨0, M.zero_mem, by ext; simp⟩
    | add y y' _ _ h h' =>
      obtain ⟨x₀, hx₀, rfl⟩ := h
      obtain ⟨x₁, hx₁, rfl⟩ := h'
      exact ⟨x₀ + x₁, M.add_mem hx₀ hx₁, by ext; simp⟩
    | smul s y _ h =>
      obtain ⟨x₀, hx₀, rfl⟩ := h
      obtain ⟨s', rfl⟩ := Ideal.Quotient.mk_surjective s
      exact ⟨s' • x₀, M.smul_mem s' hx₀, by ext; simp [π]⟩
  obtain ⟨x₀, hx₀, e⟩ := lift (fun b => π (x b)) (hS ▸ Submodule.mem_top)
  have hk : x - x₀ ∈ m • (⊤ : Submodule Γ(P₀.A.left, W) (Fin n → Γ(P₀.A.left, W))) :=
    mem_smul_top_of_forall_mem m _ fun b => by
      rw [Pi.sub_apply, ← Ideal.Quotient.eq]
      exact (congrFun e b).symm
  have : x = x₀ + (x - x₀) := by abel
  rw [this]
  exact Submodule.add_mem_sup hx₀ hk

theorem exists_dual_forms : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ W : P₀.A.left.Opens, IsAffineOpen W → ∀ a : Fin n, ∃ (N : ℕ) (g f : Fin N → Γ(P₀.A.left, W)), ∀ b, ∑ i, g i * dd b W (f i) = if a = b then 1 else 0 := by
  intro K _ _ P₀ n v dd hd W hW a
  have hmem : (Pi.single a 1 : Fin n → Γ(P₀.A.left, W)) ∈
      Submodule.span Γ(P₀.A.left, W) (Set.range fun f : Γ(P₀.A.left, W) => fun b => dd b W f) := by
    rw [span_eq_top P₀ n v dd hd W hW]; exact Submodule.mem_top
  obtain ⟨N, g, u, hu⟩ := Submodule.mem_span_set'.1 hmem
  refine ⟨N, g, fun i => (u i).2.choose, fun b => ?_⟩
  have h := congrFun hu b
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  have e : ∀ i, dd b W ((u i).2.choose) = (u i : Fin n → Γ(P₀.A.left, W)) b :=
    fun i => congrFun (u i).2.choose_spec b
  simp only [e]
  rw [h, Pi.single_apply]
  by_cases hab : a = b
  · subst hab; simp
  · rw [if_neg (Ne.symm hab), if_neg hab]

end GlobalTheory.GcDual
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.StalkDerSpan

open GlobalTheory.TangentOrigin

theorem stalk_derivation_span : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Algebra ℚ R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (p : G.left), G.hom.base p = genericPoint (Sp R) → ∀ (D : Fin n → G.left.presheaf.stalk p → G.left.presheaf.stalk p), (∀ a (W : G.left.Opens) (h : p ∈ W) (g : Γ(G.left, W)), D a (G.left.presheaf.germ W p h g) = G.left.presheaf.germ W p h (dd a W g)) → ∀ (δ : G.left.presheaf.stalk p → ResidueField (G.left.presheaf.stalk p)), (∀ u w, δ (u + w) = δ u + δ w) → (∀ u w, δ (u * w) = residue _ u * δ w + residue _ w * δ u) → (∀ r : R, δ ((G.left.presheaf.germ ⊤ p trivial).hom ((G.hom.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = 0) → ∃ c : Fin n → G.left.presheaf.stalk p, ∀ y, δ y = residue _ (∑ a, c a * D a y) := by
  intro R _ _ _ _ G _ _ hsa n v dd hinv p _ D hD δ hadd hmul hbase
  haveI : Smooth G.hom := hsa.smooth
  have hv := GlobalTheory.VertCoeffRing.isLieBasis_tvE v
  have hdd := fun (B : Type) [CommRing B] [Algebra R B] e he z O h =>
    GlobalTheory.VertCoeffRing.evalPt_lieExp (fun a => v a) dd hinv B e he z O h

  let ψ : ∀ (V : G.left.Opens), p ∈ V → Γ(G.left, V) →+* ResidueField (G.left.presheaf.stalk p) :=
    fun V hpV => (residue _).comp (G.left.presheaf.germ V p hpV).hom
  have germ_res : ∀ (V V' : G.left.Opens) (e : V' ≤ V) (hpV : p ∈ V) (hpV' : p ∈ V') (f : Γ(G.left, V)),
      G.left.presheaf.germ V' p hpV' (resG G.left e f) = G.left.presheaf.germ V p hpV f := by
    intro V V' e hpV hpV' f
    exact TopCat.Presheaf.germ_res_apply _ (homOfLE e) p hpV' f

  have loc : ∀ (V : G.left.Opens) (hpV : p ∈ V), IsAffineOpen V →
      ∃! c : Fin n → ResidueField (G.left.presheaf.stalk p),
        ∀ f, δ (G.left.presheaf.germ V p hpV f) = ∑ a, c a * ψ V hpV (dd a V f) := by
    intro V hpV hV
    obtain ⟨t, ht, et⟩ := exists_evalPt_eq hV (ψ V hpV)
    letI : Algebra R (ResidueField (G.left.presheaf.stalk p)) := (Spec.preimage (t ≫ G.hom)).hom.toAlgebra
    let y : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) (ResidueField (G.left.presheaf.stalk p)) ⟶ G :=
      Over.homMk t (Spec.map_preimage (t ≫ G.hom)).symm
    have h : ⊤ ≤ y.left ⁻¹ᵁ V := ht
    have ev : ∀ s, evalPt y.left V h s = ψ V hpV s := fun s => by
      change evalPt t V ht s = _
      rw [et]
    have hconst : ∀ r, G.left.presheaf.germ V p hpV (constFn G.hom V r) =
        (G.left.presheaf.germ ⊤ p trivial).hom ((G.hom.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
      intro r
      have e1 : constFn G.hom V r = resG G.left (le_top : V ≤ ⊤)
          ((G.hom.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
        unfold constFn
        first
          | rfl
          | (rw [Scheme.Hom.appLE_eq_app_comp_map] ; rfl)
          | (simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]; rfl)
      rw [e1]
      exact germ_res ⊤ V le_top trivial hpV _
    have := GlobalTheory.VertCoeffRing.existsUnique_coeff_alg hv hdd y hV h
      (fun f => δ (G.left.presheaf.germ V p hpV f))
      (fun f f' => by simp only [map_add (f := _), hadd])
      (fun f f' => by simp only [map_mul, hmul, ev]; rfl)
      (fun r => by rw [hconst]; exact hbase r)
    simpa only [ev] using this

  have down : ∀ (V V' : G.left.Opens) (e : V' ≤ V) (hpV : p ∈ V) (hpV' : p ∈ V')
      (c : Fin n → ResidueField (G.left.presheaf.stalk p)),
      (∀ f, δ (G.left.presheaf.germ V' p hpV' f) = ∑ a, c a * ψ V' hpV' (dd a V' f)) →
      ∀ f, δ (G.left.presheaf.germ V p hpV f) = ∑ a, c a * ψ V hpV (dd a V f) := by
    intro V V' e hpV hpV' c hc f
    rw [← germ_res V V' e hpV hpV' f, hc]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    change residue _ (G.left.presheaf.germ V' p hpV' (dd a V' (resG G.left e f))) =
      residue _ (G.left.presheaf.germ V p hpV (dd a V f))
    rw [(hinv a).1.2.2 V V' e le_top f, germ_res]
  obtain ⟨V₀, hV₀, hpV₀, -⟩ := exists_isAffineOpen_mem_and_subset (show p ∈ (⊤ : G.left.Opens) from trivial)
  obtain ⟨c₀, hc₀, hu₀⟩ := loc V₀ hpV₀ hV₀
  choose c hc using fun a => residue_surjective (R := G.left.presheaf.stalk p) (c₀ a)
  refine ⟨c, fun y => ?_⟩
  obtain ⟨W, hpW, g, rfl⟩ := TopCat.Presheaf.germ_exist _ y
  obtain ⟨V', hV', hpV', hle⟩ := exists_isAffineOpen_mem_and_subset (show p ∈ V₀ ⊓ W from ⟨hpV₀, hpW⟩)
  obtain ⟨c', hc', -⟩ := loc V' hpV' hV'
  have hcc : c' = c₀ := hu₀ c' (down V₀ V' (hle.trans inf_le_left) hpV₀ hpV' c' hc')
  subst hcc
  have eW : V' ≤ W := hle.trans inf_le_right

  rw [← germ_res W V' eW hpW hpV' g, hc', map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, hc, hD]
  rfl

end GlobalTheory.StalkDerSpan
end
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

theorem _root_.GlobalTheory.T.invariant_vectorField_pullback_along_group_hom : ∀ (R : Type) [CommRing R] (G B : Over (Sp R)) [GrpObj G] [GrpObj B] [IsCommMonObj G] [IsCommMonObj B] (q : G ⟶ B) [IsMonHom q] (v : TanM (𝟙 (Sp R)) G) (u : TanM (𝟙 (Sp R)) B) (dd : Fld G.left) (e : Fld B.left), tv v ≫ q = tv u → IsInv G v dd → IsInv B u e → ∀ (V : B.left.Opens) (W : G.left.Opens), W ≤ q.left ⁻¹ᵁ V → ∀ f : Γ(B.left, V), dd W (pbT q.left f W) = pbT q.left (e V f) W := by
  first | exact @GlobalTheory.Heat.PullField.isInv_pbT_single | exact GlobalTheory.Heat.PullField.isInv_pbT_single | (intros; apply GlobalTheory.Heat.PullField.isInv_pbT_single <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_invariant_vectorField_semiAbelian_triple_affine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (v : TanM (𝟙 (Sp R)) t.G), ∃ dd : Fld t.G.left, IsInv t.G v dd := by
  first | exact @GlobalTheory.InvFieldSemiAb.exists_isInv | exact GlobalTheory.InvFieldSemiAb.exists_isInv | (intros; apply GlobalTheory.InvFieldSemiAb.exists_isInv <;> assumption)
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

theorem _root_.GlobalTheory.T.tangent_killing_weight_zero_maps_to_abelianPart_unit : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Fin n → TanM (𝟙 (Sp R)) Y.H) (u : Fin n → (epsR R ⟶ Y.H)), (∀ a, IsTangent (u a)) → (∀ a, (u a).left = (tv (v a)).left) → ∀ (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ e : Fin n → R, (∀ (V : Q.P.A.left.Opens) f, IsWt Y 0 (Y.q.left ⁻¹ᵁ V) f → ∑ a, constFn Y.H.hom _ (e a) * dd a _ f = 0) → ∀ (B : Type) [CommRing B] [IsLocalRing B] (ψ : DualNumber R →+* B), spMap ψ ≫ (GlobalTheory.SqZero.lieExp u (fun a => (TrivSqZeroExt.inr (e a) : DualNumber R)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) ≫ Y.q).left = spMap ψ ≫ (1 : epsR R ⟶ Q.P.A).left := by
  first | exact @GlobalTheory.HeatMod.TorField.lieExp_comp_q_eq_one | exact GlobalTheory.HeatMod.TorField.lieExp_comp_q_eq_one | (intros; apply GlobalTheory.HeatMod.TorField.lieExp_comp_q_eq_one <;> assumption)
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
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KSRelSymm

theorem fieldCompat : ∀ {R : Type} [CommRing R] {K : Type} [Field K] (x₀ : R →+* K) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] (m : A.left ⟶ G.left), IsGrpPullback A G (spMap x₀) m → ∀ (w : TanM (𝟙 (Sp R)) G) (e : Fld G.left), IsInv G w e → ∀ (v : epsR K ⟶ A), IsTangent v → v.left ≫ m = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR x₀) ≫ (tv w).left → ∀ (dd : ∀ O : A.left.Opens, Γ(A.left, O) → Γ(A.left, O)), GlobalTheory.KS.IsInvDer v dd → ∀ (O : G.left.Opens) (f : Γ(G.left, O)), dd (m ⁻¹ᵁ O) ((m.app O).hom f) = pbT m (e O f) (m ⁻¹ᵁ O) := @GlobalTheory.Heat.FieldCompat.invField_baseChange

theorem cechData : ∀ {R : Type} [CommRing R] {K : Type} [Field K] (x₀ : R →+* K) (P : Out.PolAV (Sp R)) {A : Over (Sp K)} [GrpObj A] (m : A.left ⟶ P.A.left), m ≫ P.A.hom = A.hom ≫ spMap x₀ → ∀ {g : ℕ} (e : Fin g → Fld P.A.left) (dd : Fin g → ∀ O : A.left.Opens, Γ(A.left, O) → Γ(A.left, O)), (∀ a, IsField ⊤ (e a)) → (∀ a (O : P.A.left.Opens) (f : Γ(P.A.left, O)), dd a (m ⁻¹ᵁ O) ((m.app O).hom f) = pbT m (e a O f) (m ⁻¹ᵁ O)) → ∀ (D : Derivation ℤ R R) (M : Matrix (Fin g) (Fin g) R), KSRel P.A (𝟙 P.A.left) P.L e ⇑D M → ∃ L : LB P.A.left, Finite L.ι ∧ L.IsLB ∧ (∀ i, IsAffineOpen (L.U i)) ∧ LBIso P.L L ∧ ∃ d : L.ι → ∀ O : P.A.left.Opens, Γ(P.A.left, O) → Γ(A.left, m ⁻¹ᵁ O), ∀ φ, GlobalTheory.KS.IsDlog m L dd φ → GlobalTheory.KS.KSCoc A.hom P.A.hom m (fun r => x₀ (D r)) L.U dd d (fun a => GlobalTheory.KS.lc A.hom (fun b => -x₀ (M a b)) φ) := @GlobalTheory.KSCechData.exists_ksCoc_of_ksRel

theorem ksRel_symm : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (P : Out.PolAV (Sp R)) (g : ℕ) (w : Module.Basis (Fin g) R (TanM (𝟙 (Sp R)) P.A)) (e : Fin g → Fld P.A.left), (∀ c, IsInv P.A (w c) (e c)) → ∀ (D : Derivation ℤ R R) (M : Matrix (Fin g) (Fin g) R), KSRel P.A (𝟙 P.A.left) P.L e ⇑D M → Mᵀ = M := by
  intro R _ _ _ _ _ _ P g w e he D M hKS
  let K := FractionRing R
  let x₀ : R →+* K := algebraMap R K
  let P₀ : Out.PolAV (Sp K) := GlobalTheory.StrictPull.polPull P (spMap x₀)
  let m : P₀.A.left ⟶ P.A.left := pullback.fst P.A.hom (spMap x₀)
  have hm : IsGrpPullback P₀.A P.A (spMap x₀) m := isGrpPullback_pullback P.A (spMap x₀)
  have := P.isAb.comm
  have := P₀.isAb.comm
  have hs : Smooth P.A.hom := P.isAb.smooth
  obtain ⟨u, hu, hul⟩ := GlobalTheory.Heat.CoeffWt.exists_isLieBasis w
  obtain ⟨v, hv, hvl⟩ := GlobalTheory.exists_isLieBasis_baseChange R K x₀ P.A P₀.A m hm hs g u hu
  choose dd hdd using fun a => (GlobalTheory.KS.InvField.main K P₀.A (v a) (hv.1 a)).1
  have hcomp : ∀ a (O : P.A.left.Opens) (f : Γ(P.A.left, O)), dd a (m ⁻¹ᵁ O) ((m.app O).hom f) = pbT m (e a O f) (m ⁻¹ᵁ O) :=
    fun a => fieldCompat x₀ m hm (w a) (e a) (he a) (v a) (hv.1 a) (by rw [hvl, hul]) (dd a) (hdd a)
  obtain ⟨L, hfin, hL, haff, hPL, d, hd⟩ := cechData x₀ P m hm.1.w e dd (fun a => (he a).1) hcomp D M hKS
  have hI : LBIso P₀.L (L.pull m) :=
    LBIso.trans P₀.isLB (pull_isLB P.isLB m) (pull_isLB hL m) (GlobalTheory.PolBaseChange.lbIso_refl P₀.isLB)
      (hPL.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl))
  obtain ⟨⟨φ, hφ⟩, hφ'⟩ := GlobalTheory.KS.DlogPol.dlog_independent K P₀ g v dd hv hdd _ m L hL hI
  obtain ⟨Θ', hsy, hΘ'⟩ := GlobalTheory.KS.Sym.exists_symm_of_ksCoc GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1
    GlobalTheory.Moduli.cube_of_isLB K P₀ g v dd hv hdd R x₀ P m L _ d _ φ hm hL haff hI (hd φ hφ) hφ
  have e1 : Θ' = -M.map x₀ := by
    rw [eq_comm, ← sub_eq_zero]
    funext b
    refine (hφ' φ hφ).2 _ ?_
    rw [GlobalTheory.LogKSBal.lc_sub]
    exact hΘ' b
  have h1 : (M.map x₀)ᵀ = M.map x₀ := by
    have h : Θ'ᵀ = Θ' := hsy
    rwa [e1, Matrix.transpose_neg, neg_inj] at h
  ext a b
  have := congrFun (congrFun h1 a) b
  simp only [Matrix.transpose_apply, Matrix.map_apply] at this
  exact IsFractionRing.injective R K this

end GlobalTheory.KSRelSymm
end
end

section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.exists_finite_cones_siegel_level_structure : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → ∀ r : ℕ, r ≤ g → ∀ μ : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → ∀ b₀ : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b₀ x y = b₀ y x) → (∀ x, x ≠ 0 → 0 < b₀ x x) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b₀ (μ c) ≤ qW W b₀ α) → ∃ (p : ℕ) (m : Fin p → ℕ) (γ : ∀ i, Fin (m i) → LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ i, IsCone id φ (γ i)) ∧ ∀ b' : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b' x y = b' y x) → (∀ x, 0 ≤ b' x x) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b' (μ c) ≤ qW W b' α) → ∃ (i : Fin p) (k : ℕ) (cf : Fin (m i) → ℕ), 0 < k ∧ k • b' = ∑ j, cf j • γ i j := by
  first | exact @GlobalTheory.Poinc.Cells.exists_finite_cones | exact GlobalTheory.Poinc.Cells.exists_finite_cones | (intros; apply GlobalTheory.Poinc.Cells.exists_finite_cones <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CovTop

namespace GlobalTheory.CoverPull

theorem cusp_pullback_existsUnique : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → (∀ σ, GoodEmb Y.d.c₂ σ → ∀ g τ k, ‖dmin ((Y.U σ).X (Y.dict σ g).1).Gm (Y.dict σ g).2 τ k‖ = 1) → (∀ σ, GoodEmb Y.d.c₂ σ → ∃ hr : (D.sp.W j).rank = D.R.r, ∀ k, ModelW (D.sp.W j) hr ((Y.U σ).X k)) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n), ∃! g, g ∈ Y.V (wtZ a n) ∧ Y.Pull f g := by
  intro D T j Y e o hT hj hG hu hm a n hD f hf
  have hL := GlobalTheory.LevGeo.laws_core D T j hT hj
  obtain ⟨hL', hbc⟩ := GlobalTheory.T.moduliLaws_coefficientFieldChange D j _ _ _ _ _ Y.c' Y.hle _ _ hL
  obtain ⟨hf', -⟩ := hbc a n hD ⟨f, hf⟩
  obtain ⟨hL₂, -, hP⟩ := GlobalTheory.DeepLaws.laws_galois_pull D T j Y e o hT hj hG hu hm
  have hpq : (T.Q.Dw j).p ≠ (T.Q.Dw j).q ∧ 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    obtain ⟨hp, hq, -⟩ := hL.dat
    obtain ⟨h1, h2⟩ := hj
    have hk := D.R.m_add_three_le_k
    rw [hp, hq]
    simp only [Ranks.sigW]
    omega
  rw [cuspW_wtZ] at hf hf'
  have hs := cusp_le_sec _ _ _ a n hf
  have hs' := cusp_le_sec _ _ _ a n hf'
  obtain ⟨g, ⟨hg, hgP⟩, huniq⟩ := (GlobalTheory.CoverSec.section_pullback_existsUnique _ _ _ _ _ _ Y.d hpq.2 hG.lev.1
    (Or.inl ⟨hpq.1, hL.levA⟩) a n).1 _ hs'
  refine ⟨g, ⟨?_, (hP a n f hs g).2 hgP⟩, fun g' hg' => huniq g' ⟨?_, (hP a n f hs g').1 hg'.2⟩⟩
  · rw [Deep.V, cuspW_wtZ]
    exact (GlobalTheory.T.cuspForm_iff_levelCover_pullback D j _ _ _ _ _ _ _ Y.d _ _ hL' hL₂ hG.lev.1 a n hD hD.2 _ hs' g hg hgP).2 hf'
  · have h := hg'.1
    rw [Deep.V, cuspW_wtZ] at h
    exact cusp_le_sec _ _ _ a n h

end GlobalTheory.CoverPull
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.oneMap_all_tuples_over_core_of_rankBound : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → IoExt R → ∀ i, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → OneMapRowR T R κ v₀ O ph i := by
  first | exact @GlobalTheory.OneMapCore.oneMapRowR_of_core_of_size | exact GlobalTheory.OneMapCore.oneMapRowR_of_core_of_size | (intros; apply GlobalTheory.OneMapCore.oneMapRowR_of_core_of_size <;> assumption)
end
