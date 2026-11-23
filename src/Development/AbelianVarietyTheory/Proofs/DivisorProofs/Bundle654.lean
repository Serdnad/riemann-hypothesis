module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCocycleFirstChernClassTateTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle612
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGenerated
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle598
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle509
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle565
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLemmaResiduallyUnipotentCayleyTransform
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle614
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle512
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle411
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
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.UnitMul
open ClsSpec

variable {R : Type} [CommRing R]

theorem glue_sec (F G : Shv R) (Rel : ∀ U : Scheme.{0}, Sec F U → Sec G U → Prop)
    (hex : ∀ (U : Scheme.{0}) (x : Sec F U), Loc U fun V g => ∃ s, Rel V (Sec.res g x) s)
    (hres : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sec F U) (s : Sec G U), Rel U x s → Rel V (Sec.res g x) (Sec.res g s))
    (huniq : ∀ (U : Scheme.{0}) (x : Sec F U) (s s' : Sec G U), Rel U x s → Rel U x s' → s = s') :
    ∃ a : ∀ U : Scheme.{0}, Sec F U → Sec G U,
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sec F U), Sec.res g (a U x) = a V (Sec.res g x)) ∧
      ∀ (U : Scheme.{0}) (x : Sec F U) (s : Sec G U), Rel U x s → a U x = s := by
  have key : ∀ (U : Scheme.{0}) (x : Sec F U), ∃ a : Sec G U,
      ∀ (V : Scheme.{0}) (g : V ⟶ U) (s : Sec G V), Rel V (Sec.res g x) s → Sec.res g a = s := by
    intro U x
    obtain ⟨S, hS, hP⟩ := hex U x
    choose s hs using hP
    obtain ⟨a, ha⟩ := (GlobalTheory.T.etaleSheafSections_ext_and_glue R G U).2 S hS s (fun V W g k hg => by
      refine huniq W (Sec.res (k ≫ g) x) _ _ ?_ (hs _ _ _)
      rw [← res_comp]
      exact hres _ _ _ _ _ (hs _ _ hg))
    refine ⟨a, fun V g s' hs' => sep ⟨S.pullback g, Scheme.etaleTopology.pullback_stable g hS, fun W k hk => ?_⟩⟩
    beta_reduce
    rw [res_comp, ha W (k ≫ g) hk]
    refine huniq W (Sec.res (k ≫ g) x) _ _ (hs _ _ _) ?_
    rw [← res_comp]
    exact hres _ _ _ _ _ hs'
  choose a ha using key
  refine ⟨a, fun V U g x => sep (ClsSpec.loc_mono (hex V (Sec.res g x)) ?_), fun U x s hs => ?_⟩
  · rintro W k ⟨s, hs⟩
    rw [ha V _ W k s hs, res_comp]
    exact ha U x W (k ≫ g) s (by rwa [← res_comp])
  · rw [← res_id (a U x)]
    exact ha U x U (𝟙 U) s (by rwa [res_id])

variable {q : ℕ} [NeZero q] {i k : ℤ} (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q k)))
  {D : Cx (ZMod q)} (ι : D ⟶ res _ (tw q i))

def Good (s : ℤ) {U : Scheme.{0}} (b : Sec (D.X s) U) (c : Sec ((res _ (tw q k)).X s) U) : Prop :=
  ∀ (V : Scheme.{0}) (g : V ⟶ U), (∀ ζ : Prim q Γ(V, ⊤),
    Sec.res g c = μ.mul V 0 s s (zero_add s) (resGen 0 ζ) (Sec.map (ι.f s) (Sec.res g b))) ∧
    (Sec.map (ι.f s) (Sec.res g b) = 0 → Sec.res g c = 0)

theorem good_res {s : ℤ} {V U : Scheme.{0}} (g : V ⟶ U) {b : Sec (D.X s) U} {c : Sec ((res _ (tw q k)).X s) U}
    (h : Good μ ι s b c) : Good μ ι s (Sec.res g b) (Sec.res g c) := by
  intro W l
  rw [res_comp, res_comp]
  exact h W (l ≫ g)

theorem good_prim (s : ℤ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (b : Sec (D.X s) U) :
    Good μ ι s b (μ.mul U 0 s s (zero_add s) (resGen 0 ζ) (Sec.map (ι.f s) b)) := by
  intro V g
  refine ⟨fun ξ => ?_, fun h0 => ?_⟩
  · rw [μ.nat, res_resGen, res_map, resGen_zero_eq ξ (ζ.map g.appTop.hom)]
  · rw [μ.nat, res_map, h0, map_zero]

theorem good_zero (s : ℤ) {U : Scheme.{0}} (b : Sec (D.X s) U) (h : Sec.map (ι.f s) b = 0) : Good μ ι s b 0 := by
  intro V g
  rw [res_zero]
  refine ⟨fun ξ => ?_, fun _ => rfl⟩
  rw [← res_map, h, res_zero, map_zero]

variable {ι} in
theorem localization₂ (hD : ∀ n U (a : Sec ((res _ (tw q i)).X n) U), (∃ b, Sec.map (ι.f n) b = a) ↔
      Loc U fun V g => IsUnit (q : Γ(V, ⊤)) ∨ Sec.res g a = 0)
    {s : ℤ} {U : Scheme.{0}} (b : Sec (D.X s) U) :
    Loc U fun V g => Nonempty (Prim q Γ(V, ⊤)) ∨ Sec.map (ι.f s) (Sec.res g b) = 0 := by
  have h1 := (hD s U (Sec.map (ι.f s) b)).1 ⟨b, rfl⟩
  refine ClsSpec.loc_trans (ClsSpec.loc_mono h1 fun V g h => ?_)
  rcases h with hu | h0
  · exact ClsSpec.loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).1 hu) fun W l ⟨ζ⟩ => Or.inl ⟨ζ⟩
  · rw [res_map] at h0
    exact GlobalTheory.T.etaleLocal_property_calculus_rules.1 V _ fun W l => Or.inr (by rw [← res_comp, ← res_map, h0, res_zero])

end GlobalTheory.EtC.UnitMul

namespace GlobalTheory.EtC.UnitMul
open ClsSpec

variable {R : Type} [CommRing R]

variable {q : ℕ} [NeZero q] {i k : ℤ} (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q k)))
  {D : Cx (ZMod q)} (ι : D ⟶ res _ (tw q i))

theorem res_smul {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (r : ULift.{1} R) (a : Sec F U) :
    Sec.res g (r • a) = r • Sec.res g a := map_smul _ _ _
theorem smap_smul {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (r : ULift.{1} R) (a : Sec F U) :
    Sec.map φ (r • a) = r • Sec.map φ a := map_smul _ _ _

variable {ι} in
theorem good_uniq (hD : ∀ n U (a : Sec ((res _ (tw q i)).X n) U), (∃ b, Sec.map (ι.f n) b = a) ↔
      Loc U fun V g => IsUnit (q : Γ(V, ⊤)) ∨ Sec.res g a = 0)
    {s : ℤ} {U : Scheme.{0}} (b : Sec (D.X s) U) (c c' : Sec ((res _ (tw q k)).X s) U)
    (hc : Good μ ι s b c) (hc' : Good μ ι s b c') : c = c' :=
  sep (ClsSpec.loc_mono (localization₂ hD b) fun V g h => h.elim (fun ⟨ζ⟩ => ((hc V g).1 ζ).trans ((hc' V g).1 ζ).symm)
    (fun h0 => ((hc V g).2 h0).trans ((hc' V g).2 h0).symm))


variable {ι} in
theorem exists_fam (hD : ∀ n U (a : Sec ((res _ (tw q i)).X n) U), (∃ b, Sec.map (ι.f n) b = a) ↔
      Loc U fun V g => IsUnit (q : Γ(V, ⊤)) ∨ Sec.res g a = 0) (s : ℤ) :
    ∃ a : ∀ U : Scheme.{0}, Sec (D.X s) U → Sec ((res _ (tw q k)).X s) U,
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sec (D.X s) U), Sec.res g (a U x) = a V (Sec.res g x)) ∧
      ∀ (U : Scheme.{0}) (x : Sec (D.X s) U) (c : Sec ((res _ (tw q k)).X s) U), Good μ ι s x c → a U x = c :=
  glue_sec _ _ (fun U x c => Good μ ι s x c)
    (fun U x => ClsSpec.loc_mono (localization₂ hD x) fun V g h => h.elim (fun ⟨ζ⟩ => ⟨_, good_prim μ ι s ζ _⟩)
      (fun h0 => ⟨0, good_zero μ ι s _ h0⟩))
    (fun V U g x c h => good_res μ ι g h)
    (fun U x c c' h h' => good_uniq μ hD x c c' h h')

end GlobalTheory.EtC.UnitMul


open GlobalTheory.EtC.UnitMul ClsSpec in
theorem GlobalTheory.EtC.unit_mul_chain_map : ∀ (q : ℕ) [NeZero q] (i k : ℤ) (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q k)))
    (D : Cx (ZMod q)) (ι : D ⟶ res _ (tw q i)), (∀ n U (a : Sec ((res _ (tw q i)).X n) U),
      (∃ b, Sec.map (ι.f n) b = a) ↔ Loc U fun V g => IsUnit (q : Γ(V, ⊤)) ∨ Sec.res g a = 0) →
    ∃ u : D ⟶ res _ (tw q k), ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (s : ℤ) (b : Sec (D.X s) U),
      Sec.map (u.f s) b = μ.mul U 0 s s (zero_add s) (resGen 0 ζ) (Sec.map (ι.f s) b) := by
  intro q _ i k μ D ι hD
  choose a ha hs using exists_fam μ hD
  have aP : ∀ (s : ℤ) (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (x : Sec (D.X s) U),
      a s U x = μ.mul U 0 s s (zero_add s) (resGen 0 ζ) (Sec.map (ι.f s) x) :=
    fun s U ζ x => hs s U x _ (good_prim μ ι s ζ x)
  have aZ : ∀ (s : ℤ) (U : Scheme.{0}) (x : Sec (D.X s) U), Sec.map (ι.f s) x = 0 → a s U x = 0 :=
    fun s U x h => hs s U x 0 (good_zero μ ι s x h)
  have aAdd : ∀ (s : ℤ) (U : Scheme.{0}) (x y : Sec (D.X s) U), a s U (x + y) = a s U x + a s U y := by
    intro s U x y
    refine sep (ClsSpec.loc_mono (ClsSpec.loc_and (localization₂ hD x) (localization₂ hD y)) fun V g h => ?_)
    rw [res_add, ha, ha, ha, res_add]
    rcases h with ⟨⟨⟨ζ⟩⟩ | hx, ⟨⟨ζ⟩⟩ | hy⟩
    · rw [aP s V ζ, aP s V ζ, aP s V ζ, smap_add, map_add (f := _)]
    · rw [aP s V ζ, aP s V ζ, aP s V ζ, smap_add, map_add (f := _)]
    · rw [aP s V ζ, aP s V ζ, aP s V ζ, smap_add, map_add (f := _)]
    · rw [aZ s V _ hx, aZ s V _ hy, aZ s V _ (by rw [smap_add, hx, hy, add_zero]), add_zero]
  have aSmul : ∀ (s : ℤ) (U : Scheme.{0}) (r : ULift.{1} (ZMod q)) (x : Sec (D.X s) U), a s U (r • x) = r • a s U x := by
    intro s U r x
    refine sep (ClsSpec.loc_mono (localization₂ hD x) fun V g h => ?_)
    rw [res_smul, ha, ha, res_smul]
    rcases h with ⟨⟨ζ⟩⟩ | hx
    · rw [aP s V ζ, aP s V ζ, smap_smul, map_smul]
    · rw [aZ s V _ hx, aZ s V _ (by rw [smap_smul, hx, smul_zero]), smul_zero]
  have aD : ∀ (s : ℤ) (U : Scheme.{0}) (x : Sec (D.X s) U),
      Sec.map ((res _ (tw q k)).d s (s + 1)) (a s U x) = a (s + 1) U (Sec.map (D.d s (s + 1)) x) := by
    intro s U x
    have hι : ∀ {V : Scheme.{0}} (y : Sec (D.X s) V), Sec.map ((res _ (tw q i)).d s (s + 1)) (Sec.map (ι.f s) y) =
        Sec.map (ι.f (s + 1)) (Sec.map (D.d s (s + 1)) y) := fun y => by
      rw [map_comp, ι.comm, ← map_comp]
    refine sep (ClsSpec.loc_mono (localization₂ hD x) fun V g h => ?_)
    rw [res_map, ha, ha, res_map]
    rcases h with ⟨⟨ζ⟩⟩ | hx
    · rw [aP s V ζ, aP (s + 1) V ζ, μ.leibniz, ← hι]
      have h0 : Sec.map ((res _ (tw q 0)).d 0 (0 + 1)) (resGen 0 ζ) = 0 := d_resGen 0 ζ
      rw [h0, map_zero, LinearMap.zero_apply, zero_add, Int.negOnePow_zero, one_smul]
    · rw [aZ s V _ hx, smap_zero, aZ (s + 1) V _ (by rw [← hι, hx, smap_zero])]
  let F : ∀ s : ℤ, D.X s ⟶ (res _ (tw q k)).X s := fun s =>
    ⟨{ app := fun X => ModuleCat.ofHom
          { toFun := a s X.unop
            map_add' := aAdd s X.unop
            map_smul' := aSmul s X.unop }
       naturality := fun X Y f => by
          apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
          exact (ha s Y.unop X.unop f.unop x).symm }⟩
  refine ⟨{ f := F, comm' := fun s t hst => ?_ }, fun U ζ s b => aP s U ζ b⟩
  change s + 1 = t at hst
  subst hst
  apply Sheaf.hom_ext; ext X x
  exact aD s X.unop x
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_alexanderWhitneyDiagonal_swap_homotopy : ∃ h : ∀ N, Pr N →₀ ℤ, (∀ N, Pr.Deg (N + 1) (h N)) ∧ Pr.d 0 (h 0) = Pr.aw 0 - Pr.wa 0 ∧ ∀ N, Pr.d (N + 1) (h (N + 1)) + Pr.bd (h N) = Pr.aw (N + 1) - Pr.wa (N + 1) := by
  first | exact @GlobalTheory.EtC.pr_aw_wa_homotopy | exact GlobalTheory.EtC.pr_aw_wa_homotopy | (intros; apply GlobalTheory.EtC.pr_aw_wa_homotopy <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.freeEtaleModuleSheaf_map_mono_epi_iso : ∀ (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q), (Mono f → Mono ((free R).map f)) ∧ ((∀ U (y : Q.obj (op U)), Loc U fun V g => ∃ x, f.app (op V) x = Q.map g.op y) → Epi ((free R).map f)) ∧ ((∀ U (y : Q.obj (op U)), Loc U fun V g => ∃ x, f.app (op V) x = Q.map g.op y) → (∀ U (x x' : P.obj (op U)), f.app (op U) x = f.app (op U) x' → Loc U fun _ g => P.map g.op x = P.map g.op x') → IsIso ((free R).map f)) := by
  first | (exact @GlobalTheory.EtC.free_map_mono_epi_iso) | (exact GlobalTheory.EtC.free_map_mono_epi_iso) | (intros; apply GlobalTheory.EtC.free_map_mono_epi_iso  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.sectionsComplex_exact_etaleLocally_of_no_classes : ∀ (R : Type) [CommRing R] (M : Cx R) (U : Scheme.{0}), (∀ n, Subsingleton (CohomologyClass ((chains R).obj (sch.obj U)) M n)) → ∀ (n : ℤ) (b : Sec (M.X n) U), Sec.map (M.d n (n + 1)) b = 0 → Loc U fun V g => ∃ a : Sec (M.X (n - 1)) V, Sec.map (M.d (n - 1) n) a = Sec.res g b := by
  first | (exact @GlobalTheory.EtC.sch_loc_exact) | (exact GlobalTheory.EtC.sch_loc_exact) | (intros; apply GlobalTheory.EtC.sch_loc_exact <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.tensor_flat_etaleSheaf_preserves_local_exactness : ∀ (R : Type) [CommRing R] (M : Shv R), FlatS M → ∀ {A B C : Shv R} (f : A ⟶ B) (g : B ⟶ C), f ≫ g = 0 → (∀ U (b : Sec B U), Sec.map g b = 0 → Loc U fun V k => ∃ a : Sec A V, Sec.map f a = Sec.res k b) → ∀ U (x : TensorProduct (ULift.{1} R) (Sec B U) (Sec M U)), (Loc U fun V k => LinearMap.rTensor _ (g.hom.app (op V)).hom (TensorProduct.map (B.obj.map k.op).hom (M.obj.map k.op).hom x) = 0) → Loc U fun V k => ∃ y : TensorProduct (ULift.{1} R) (Sec A V) (Sec M V), LinearMap.rTensor _ (f.hom.app (op V)).hom y = TensorProduct.map (B.obj.map k.op).hom (M.obj.map k.op).hom x := by
  first | (exact @GlobalTheory.EtC.tensor_flat_loc_exact) | (exact GlobalTheory.EtC.tensor_flat_loc_exact) | (intros; apply GlobalTheory.EtC.tensor_flat_loc_exact  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.tateTwist_sections_locally_generated : ∀ (q : ℕ) [NeZero q] (i : ℤ), (∀ (U : Scheme.{0}) (y : Sec (tw q i) U), Loc U fun V g => Sec.res g y = 0 ∨ ∃ (ζ : Prim q Γ(V, ⊤)) (c : ℕ), Sec.res g y = c • twGen i ζ) ∧ (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U), Loc U fun V g => ∃ c : ℕ, Sec.res g y = c • twGen i (ζ.map g.appTop.hom)) ∧ (∀ (U : Scheme.{0}) [Nonempty U] (ζ : Prim q Γ(U, ⊤)) (c : ℕ), c • twGen i ζ = 0 → q ∣ c) ∧ (∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)), Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom)) ∧ (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val → twGen i ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • twGen i ζ) ∧ ∀ (M : Shv (ZMod q)) (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec M U), (∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom)) → (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val → e U ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • e U ζ) → ∃! φ : tw q i ⟶ M, ∀ U ζ, Sec.map φ (twGen i ζ) = e U ζ := by
  first | (exact @GlobalTheory.EtC.twist_sections) | (exact GlobalTheory.EtC.twist_sections) | (intros; apply GlobalTheory.EtC.twist_sections  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory

def coneSES {R : Type} [CommRing R] {C J : Cx R} (u : C ⟶ J) (t : ℤ) : ShortComplex (Shv R) :=
  ShortComplex.mk ((mappingCone.inr u).f t) ((mappingCone.fst u).1.v t (t + 1) rfl) (by simp)

def coneSESSplitting {R : Type} [CommRing R] {C J : Cx R} (u : C ⟶ J) (t : ℤ) : (coneSES u t).Splitting where
  r := (mappingCone.snd u).v t t (add_zero t)
  s := (mappingCone.inl u).v (t + 1) t (by omega)
  f_r := by simp [coneSES]
  s_g := by simp [coneSES]
  id := by
    rw [add_comm]
    exact mappingCone.id_X u t (t + 1) rfl

theorem coneSES_shortExact {R : Type} [CommRing R] {C J : Cx R} (u : C ⟶ J) (t : ℤ) : (coneSES u t).ShortExact :=
  (coneSESSplitting u t).shortExact

theorem sgl_isKInjective {R : Type} [CommRing R] (I : Shv R) [Injective I] : (sgl I).IsKInjective := by
  haveI : ∀ n, Injective ((sgl I).X n) := by
    intro n
    by_cases h : n = 0
    · subst h
      exact Injective.of_iso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 I).symm inferInstance
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 I n h).injective
  exact CochainComplex.isKInjective_of_injective _ 0

theorem sgl_cohomologyClass_subsingleton {R : Type} [CommRing R] (G I : Shv R) (i : ℤ) (hi : i ≠ 0) :
    Subsingleton (CohomologyClass (sgl G) (sgl I) i) := by
  have hc : ∀ a b : Cochain (sgl G) (sgl I) i, a = b := by
    intro a b
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    by_cases hp : p = 0
    · have hq : q ≠ 0 := by omega
      exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 I q hq).eq_of_tgt _ _
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 G p hp).eq_of_src _ _
  constructor
  intro x y
  obtain ⟨a, rfl⟩ := x.mk_surjective
  obtain ⟨b, rfl⟩ := y.mk_surjective
  exact congrArg CohomologyClass.mk (Cocycle.ext (hc _ _))

theorem ext_injective_subsingleton {R : Type} [CommRing R] (G I : Shv R) [Injective I] (i : ℤ) (hi : i ≠ 0) :
    Subsingleton (CohomologyClass (sgl G) (res R I) i) := by
  obtain ⟨hK, -, -, hq, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R I
  haveI := hK
  haveI := hq
  haveI := sgl_isKInjective I
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff (resAug I)).1 hq
  have h63 := GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R
  have hsurj : Function.Surjective (cpush (sgl G) (resAug I) i) := by
    intro y
    refine ⟨cpush (sgl G) e.inv i y, ?_⟩
    rw [← h63.2.2.1 (sgl G) e.inv (resAug I) i y, ← he,
      (h63.2.2.2.2 _ _ ⟨e.homotopyInvHomId⟩ (sgl G) i).2, (h63.1 (sgl G) _ i y).2]
  haveI := sgl_cohomologyClass_subsingleton G I i hi
  constructor
  intro x y
  obtain ⟨x', rfl⟩ := hsurj x
  obtain ⟨y', rfl⟩ := hsurj y
  rw [Subsingleton.elim x' y']

theorem cone_terms_ext_subsingleton : ∀ (R : Type) [CommRing R] (G : Shv R) {C J : Cx R} (u : C ⟶ J),
    (∀ t, Injective (J.X t)) → (∀ t i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R (C.X t)) i)) →
    ∀ t i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R ((mappingCone u).X t)) i) := by
  intro R _ G C J u hJ hC t i hi
  obtain ⟨z, hz⟩ := GlobalTheory.T.etaleCohomology_coefficient_longExactSequence R (coneSES u t) (coneSES_shortExact u t)
  have hex := (hz (sgl G) i).1
  haveI := hJ t
  haveI hsJ : Subsingleton (CohomologyClass (sgl G) (res R (J.X t)) i) := ext_injective_subsingleton G (J.X t) i hi.ne'
  haveI hsC : Subsingleton (CohomologyClass (sgl G) (res R (C.X (t + 1))) i) := hC (t + 1) i hi
  constructor
  intro x y
  obtain ⟨w, hw⟩ := (hex x).1 (Subsingleton.elim (α := CohomologyClass (sgl G) (res R (C.X (t + 1))) i) _ _)
  obtain ⟨w', hw'⟩ := (hex y).1 (Subsingleton.elim (α := CohomologyClass (sgl G) (res R (C.X (t + 1))) i) _ _)
  rw [← hw, ← hw', @Subsingleton.elim _ hsJ w w']

end GlobalTheory

end
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

theorem natSeq_pow_of_mul_eq {p h : ℕ} (hp : p.Prime) (a b : ℕ → ℕ)
    (hab : ∀ n, a n * b n = p ^ (n * h))
    (ha : ∀ n, a (n + 1) ≤ a 1 * a n) (hb : ∀ n, b (n + 1) ≤ b 1 * b n) :
    ∃ s : ℕ, ∀ n, a n = p ^ (n * s) := by
  have h1 : a 1 * b 1 = p ^ h := by simpa using hab 1
  obtain ⟨s, hs, hs'⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro _ h1)
  obtain ⟨t, ht, ht'⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro_left _ h1)
  have h0 : a 0 * b 0 = 1 := by simpa using hab 0
  have ha0 : a 0 = 1 := Nat.eq_one_of_mul_eq_one_right h0
  have hb0 : b 0 = 1 := Nat.eq_one_of_mul_eq_one_left h0
  have hst : s + t = h := by
    rw [hs', ht', ← pow_add] at h1
    exact Nat.pow_right_injective hp.two_le h1
  have hale : ∀ n, a n ≤ p ^ (n * s) := by
    intro n
    induction n with
    | zero => simp [ha0]
    | succ n ih =>
      calc a (n + 1) ≤ a 1 * a n := ha n
        _ ≤ p ^ s * p ^ (n * s) := by rw [hs']; exact Nat.mul_le_mul_left _ ih
        _ = p ^ ((n + 1) * s) := by rw [← pow_add]; ring_nf
  have hble : ∀ n, b n ≤ p ^ (n * t) := by
    intro n
    induction n with
    | zero => simp [hb0]
    | succ n ih =>
      calc b (n + 1) ≤ b 1 * b n := hb n
        _ ≤ p ^ t * p ^ (n * t) := by rw [ht']; exact Nat.mul_le_mul_left _ ih
        _ = p ^ ((n + 1) * t) := by rw [← pow_add]; ring_nf
  refine ⟨s, fun n => ?_⟩
  by_contra hne
  have hlt : a n < p ^ (n * s) := lt_of_le_of_ne (hale n) hne
  have hpos : 0 < p ^ (n * t) := pow_pos hp.pos _
  have key : a n * b n < p ^ (n * s) * p ^ (n * t) :=
    calc a n * b n ≤ a n * p ^ (n * t) := Nat.mul_le_mul_left _ (hble n)
      _ < p ^ (n * s) * p ^ (n * t) := Nat.mul_lt_mul_of_pos_right hlt hpos
  rw [hab n, ← pow_add, ← Nat.mul_add, hst] at key
  exact lt_irrefl _ key

theorem kerIdeal_finrank_eq_pow_of_idempotent : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    (G : PDivGroup p k) (u v : G ⟶ G), u + v = 𝟙 G → u ≫ v = 0 → v ≫ u = 0 →
    ∃ h₀ : ℕ, ∀ n : ℕ, Module.finrank k (G.A n ⧸ kerIdeal (u.app n)) = p ^ (n * h₀) := by
  intro p _ k _ G u v huv h1 h2
  exact natSeq_pow_of_mul_eq (Fact.out : p.Prime)
    (fun n => Module.finrank k (G.A n ⧸ kerIdeal (u.app n)))
    (fun n => Module.finrank k (G.A n ⧸ kerIdeal (v.app n)))
    (GlobalTheory.T.finrank_kernelIdeal_mul_of_idempotents p k G u v huv h1 h2)
    (GlobalTheory.T.finrank_kernelIdeal_succ_le_mul_levels p k G u) (GlobalTheory.T.finrank_kernelIdeal_succ_le_mul_levels p k G v)

end GlobalTheory
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.dvd_of_forall_invariantDifferential_dvd : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (n : ℕ) (a : O) (b : G.A n), (∀ (w : G.dual.omega) (φ : CartierDual O (G.A n)), dUnit (R := O) φ = w.1 n → a ∣ φ b) → (∃ z, b = a • z) ∧ ∀ w : G.dual.omega, ∃ φ : CartierDual O (G.A n), dUnit (R := O) φ = w.1 n := by
  first | exact @GlobalTheory.PDivGroup.dvd_of_forall_omega_dvd | exact GlobalTheory.PDivGroup.dvd_of_forall_omega_dvd | (intros; apply GlobalTheory.PDivGroup.dvd_of_forall_omega_dvd <;> assumption)
end

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem natCast_isInt {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (n : ℕ) :
    0 ≤ v (n : C) := by
  induction n with
  | zero => simp
  | succ k ih =>
    push_cast
    refine le_trans (le_min ih (by simp)) (v.map_add _ _)

theorem intCast_isInt {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (n : ℤ) :
    0 ≤ v (n : C) := by
  cases n with
  | ofNat k => simpa using natCast_isInt v k
  | negSucc k =>
    rw [Int.cast_negSucc, v.map_neg]
    exact_mod_cast natCast_isInt v (k + 1)

theorem detDepth_bounds : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → v (p : C) = 1 → ∀ (i d c : ℕ) (G : LogFGL v d) (u : Fin i → Fin d → C),
    IsSatFrame v u → 0 ≤ detDepth G u c ∧ detDepth G u c ≤ content v (detPow C i c) ∧
    detDepth G u c ≤ (((i * c : ℝ) / (p - 1) : ℝ) : EReal) := by
  intro C _ _ v p hp hv i d c G u hu
  obtain ⟨hhom, hint, -, -⟩ := GlobalTheory.T.matrixVariablesDeterminantPow_monomial_shape C i c
  have h0 : 0 ≤ detDepth G u c := by
    unfold detDepth
    exact GlobalTheory.T.depth_nonneg_integral_operator_integral_vectors C v (Fin i) (fun _ => d) (fun _ => G) (fun _ => Fin i) (fun _ => u)
      (detPow C i c) (fun _ a e => hu.1 a e)
      (fun α => by obtain ⟨n, hn⟩ := hint α; rw [hn]; exact intCast_isInt v n)
  have h1 : detDepth G u c ≤ content v (detPow C i c) := by
    unfold detDepth
    exact GlobalTheory.T.differentialOperatorDepth_le_dividedPowerContent C v (Fin i) (fun _ => d) (fun _ => i) (fun _ => G) (fun _ => u)
      (detPow C i c) (i * c) hhom (fun _ => hu)
  exact ⟨h0, h1, h1.trans (GlobalTheory.T.dividedPowerContentValuation_detPow_bounds C v p hp hv i c).1⟩

end GlobalTheory.FGDepth
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.unitLemma_residuallyUnipotent_cayleyTransform : UnitLemmaLie → ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → ∀ s : K.Oˣ, algebraMap K.O K.E s * K.c (algebraMap K.O K.E s) = 1 → (∃ Q : K.O[X], Q.map (algebraMap K.O K.E) = B₁.P * B₂.P ∧ Q.map (IsLocalRing.residue K.O) = (X - C (IsLocalRing.residue K.O s)) ^ Q.natDegree) → InvAlg.Identity B₁ B₂ := by
  first | exact @GlobalTheory.UnitLemma.CayleyAny.identity_of_residually_unipotent_any | exact GlobalTheory.UnitLemma.CayleyAny.identity_of_residually_unipotent_any | (intros; apply GlobalTheory.UnitLemma.CayleyAny.identity_of_residually_unipotent_any <;> assumption)
end

section

open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData

theorem _root_.GlobalTheory.T.cuspidal_unipotent_vanishing : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GlobalTheory.SmGL.IsCuspidal π → ∀ (a b : ℕ) (e : Fin N ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ u : (Fin a → Fin b → k) → GL (Fin N) k, (∀ X, (u X : Matrix (Fin N) (Fin N) k) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) → ∀ w : V, w ∈ Submodule.span ℂ {x | ∃ (Y : Fin a → Fin b → k) (y : V), x = π (u Y) y - y} := by
  first | exact @GlobalTheory.SmGL.CuspSpan.mem_span_unip | exact GlobalTheory.SmGL.CuspSpan.mem_span_unip | (intros; apply GlobalTheory.SmGL.CuspSpan.mem_span_unip <;> assumption)
end
