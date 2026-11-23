module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.BesselDatum
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle296
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle306
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle322
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle187
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle324
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle325
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle312
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassNumberDvdHstar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle327
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.LocalToGlobal.Columns.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RootExch.CoefInt

theorem coeff_integrable_continuous : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ ν 𝓝, d.IsUnitPair ν 𝓝 → ∀ F : GA D B → ℂ, Continuous F → (∀ γ ∈ GQ B, ∀ g, F (γ * g) = F g) → (∀ g, IntegrableOn (fun n : d.N => F ((n : GA D B) * g) * star (d.psiN ψ (n : GA D B))) 𝓝 ν) ∧ Continuous (d.coeff ψ ν 𝓝 F) ∧ ∀ C : Set (GA D B), IsCompact C → ∃ M : ℝ, ∀ n ∈ d.N, ∀ g ∈ C, ‖F (n * g)‖ ≤ M :=
  coeff_integrable_continuous_of fun D B ρ e he => (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B ρ e he).1

end GlobalTheory.RootExch.CoefInt
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

noncomputable section

namespace GlobalTheory.DefU

theorem prod_list_apply_multilinear {ι G V : Type} [DecidableEq ι] [Group G] [AddCommGroup V] [Module ℂ V]
    {H : ι → Type} [∀ v, Group (H v)] {Wv : ι → Type} [∀ v, AddCommGroup (Wv v)] [∀ v, Module ℂ (Wv v)]
    (ρ : Representation ℂ G V) (s : ∀ v, H v →* G) (σ : ∀ v, Representation ℂ (H v) (Wv v))
    (F : (∀ v, Wv v) →ₘₗ[ℂ] V)
    (hF : ∀ v (h : H v) (x : ∀ u, Wv u), ρ (s v h) (F x) = F (Function.update x v (σ v h (x v))))
    (y : ∀ v, H v) (u : ∀ v, Wv v) :
    ∀ L : List ι, L.Nodup →
      ρ (L.map fun v => s v (y v)).prod (F u) = F fun v => if v ∈ L then σ v (y v) (u v) else u v := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons a L ih =>
    intro hL
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.prod_cons, map_mul, mul_apply_eq_comp, ih hL.2, hF]
    congr 1
    funext v
    by_cases hv : v = a
    · rw [hv, Function.update_self]
      simp [hL.1]
    · rw [Function.update_of_ne hv]
      simp [hv]

theorem AutSub.finPart_wt_ne_bot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n),
    π.finPart (AU.mk π).wt ≠ ⊥ := by
  intro E _ _ _ n π
  classical
  have hW' : ∀ v : InfinitePlace E, HasWeightAt π.V v.embedding ((AU.mk π).wt v) := fun v => by
    obtain ⟨lam, hlam, -⟩ := GlobalTheory.T.existsUnique_weight_definiteUnitary_at E n (AU.mk π) v.embedding
    have h := hlam.wt
    rw [Wt.at_embedding] at h
    exact (AU.hasWt_mk π _ _).1 h
  generalize (AU.mk π).wt = W at hW' ⊢
  have hW := hW'
  clear hW'
  let s : ∀ v : InfinitePlace E, embU n v.embedding →* UA E n := fun v => (embU n v.embedding).subtype
  let σ : ∀ v : InfinitePlace E, Representation ℂ (embU n v.embedding) (nablaSq ℂ n (W v)) := fun v =>
    (GlobalTheory.Branching.sqRep ℂ n (W v)).comp ((cEmb v.embedding).comp (embU n v.embedding).subtype)
  have hirr : ∀ v, (σ v).IsIrreducible := fun v => by
    obtain ⟨e, he⟩ := GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E n v.embedding
    obtain ⟨h1, h2⟩ := (CuspRep.isIrreducible_iff _).1 (GlobalTheory.Branching.isIrreducible_smallRep_unitary n (W v))
    refine (CuspRep.isIrreducible_iff _).2 ⟨h1, fun S hS => h2 S fun g w hw => ?_⟩
    obtain ⟨x, rfl⟩ := e.surjective g
    have := hS x w hw
    change GlobalTheory.Branching.sqRep ℂ n (W v) (cEmb v.embedding (x : UA E n)) w ∈ S at this
    change GlobalTheory.Branching.sqRep ℂ n (W v) (GlobalTheory.Branching.unitaryIncl n (e x)) w ∈ S
    rwa [he]
  have hcomm : ∀ u v, u ≠ v → ∀ a b, Commute (s u a) (s v b) := fun u v huv a b =>
    GlobalTheory.T.commute_unitaryArchimedeanPoints_distinct_places E n u.embedding v.embedding (by rwa [InfinitePlace.mk_embedding, InfinitePlace.mk_embedding])
      _ a.2 _ b.2
  have hspan : ∀ v, (⨆ f : (σ v).IntertwiningMap (π.rep.comp (s v)), LinearMap.range f.toLinearMap) = ⊤ :=
    fun v => GlobalTheory.T.iSup_range_weightMaps_eq_top_definiteUnitary E n π v.embedding (W v) (hW v)
  have hV : Nontrivial π.V := Submodule.nontrivial_iff_ne_bot.2 π.isAut.ne_bot
  obtain ⟨F, hF0, hF⟩ := GlobalTheory.T.exists_multilinearMap_of_isotypic_commuting_subgroups (InfinitePlace E) (UA E n) π.V (fun v => embU n v.embedding)
    (fun v => nablaSq ℂ n (W v)) π.rep s σ hV hirr hcomm hspan
  let B := Formalism.L2.DIV.bVV ℂ W
  let b := fun v => GlobalTheory.CoefIrred.ssBasis ℂ (W v)
  have hB : ∀ i, B i = GlobalTheory.CoefIrred.tenMul W (fun v => b v (i v)) := by
    intro i
    apply Subtype.ext
    rw [Formalism.L2.DIV.bVV_coe, GlobalTheory.CoefIrred.tenMul_coe, Formalism.L2.DIV.bVVfun]
    simp only [b, GlobalTheory.CoefIrred.ssBasis_coe]
  let f0 : W.Sp →ₗ[ℂ] π.V := B.constr ℂ (fun i => F (fun v => b v (i v)))
  have hf0 : ∀ u, f0 (GlobalTheory.CoefIrred.tenMul W u) = F u := by
    have hComp : f0.compMultilinearMap (GlobalTheory.CoefIrred.tenMul W) = F := by
      apply Module.Basis.ext_multilinear b
      intro i
      simp only [LinearMap.compMultilinearMap_apply, ← hB, f0, Module.Basis.constr_basis]
    intro u
    exact congrArg (fun m => m u) hComp
  let f : W.Sp →ₗ[ℂ] (UA E n → ℂ) := π.V.subtype ∘ₗ f0
  have hten : ∀ (g : InfinitePlace E → GL (Fin n) ℂ) (u : ∀ v, nablaSq ℂ n (W v)),
      Formalism.L2.DIV.rhoK W g (GlobalTheory.CoefIrred.tenMul (K := ℂ) W u) =
        GlobalTheory.CoefIrred.tenMul (K := ℂ) W fun v => GlobalTheory.Branching.sqRep ℂ n (W v) (g v) (u v) := fun g u => by
    apply Subtype.ext
    rw [Formalism.L2.DIV.rhoK_coe, GlobalTheory.CoefIrred.tenMul_coe, Formalism.L2.DIV.actTen, GlobalTheory.CoefIrred.tenMul_coe]
    rfl
  have hint : ∀ (x : infU E n) (w : W.Sp), f (W.rep x w) = RU E n x (f w) := by
    intro x w
    obtain ⟨y, hy, hyc, hprod⟩ := GlobalTheory.T.definiteUnitaryInfinitePoint_eq_list_prod_placeParts E n x.1 x.2
    let y' : ∀ v : InfinitePlace E, embU n v.embedding := fun v => ⟨y v, hy v⟩
    have key : ∀ u, f (W.rep x (GlobalTheory.CoefIrred.tenMul W u)) = RU E n x (f (GlobalTheory.CoefIrred.tenMul W u)) := by
      intro u
      have h1 := prod_list_apply_multilinear π.rep s σ F hF y' u Finset.univ.toList (Finset.nodup_toList _)
      have h2 : (Finset.univ.toList.map fun v => s v (y' v)).prod = x.1 := hprod
      rw [h2] at h1
      have h3 : W.rep x (GlobalTheory.CoefIrred.tenMul W u) = GlobalTheory.CoefIrred.tenMul W fun v => σ v (y' v) (u v) := by
        change Formalism.L2.DIV.rhoK W (cAll x.1) _ = _
        rw [hten]
        refine congrArg (GlobalTheory.CoefIrred.tenMul W) (funext fun v => ?_)
        change _ = GlobalTheory.Branching.sqRep ℂ n (W v) (cEmb v.embedding (y v)) (u v)
        rw [hyc v]
        rfl
      show (f0 (W.rep x (GlobalTheory.CoefIrred.tenMul W u))).1 = RU E n x (f0 (GlobalTheory.CoefIrred.tenMul W u)).1
      rw [h3, hf0, hf0, ← AutSub.rep_val, h1]
      simp only [Finset.mem_toList, Finset.mem_univ, ite_true]
    have heq : f ∘ₗ W.rep x = RU E n x ∘ₗ f := by
      apply B.ext
      intro i
      rw [hB]
      exact key _
    exact LinearMap.congr_fun heq w
  have hmem : f ∈ algForms W := ⟨fun w => π.le_autU (f0 w).2, hint⟩
  have hfin : (⟨f, hmem⟩ : algForms W) ∈ π.finPart W := AutSub.mem_finPart.2 fun w => (f0 w).2
  obtain ⟨u, hu⟩ : ∃ u, F u ≠ 0 := by
    by_contra h
    push Not at h
    exact hF0 (MultilinearMap.ext h)
  refine (Submodule.ne_bot_iff _).2 ⟨⟨f, hmem⟩, hfin, fun h => hu ?_⟩
  have := LinearMap.congr_fun (congrArg Subtype.val h) (GlobalTheory.CoefIrred.tenMul W u)
  rw [← hf0]
  exact Subtype.ext this

end GlobalTheory.DefU

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.Mem.RayRoots

theorem rootOne_mem_of_isRayFieldIn : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (φ : E →+* ℂ)
    (N n : ℕ) (M : IntermediateField ℚ ℂ), N ≠ 0 → n ∣ N → IsRayFieldIn φ (natIdeal E N) M → rootOne n ∈ M :=
  fun _ _ _ _ φ _ _ _ hN hn hM => GlobalTheory.Mem.FieldsEx.rootOne_mem_ray φ hN hn hM

end GlobalTheory.Mem.RayRoots
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 Matrix
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_periodPair_lattice_eq_lamOf : ∀ (R : Ranks) (H : Host R), ∃ (δ : ℂ) (L : PeriodPair) (ω₀ : ℂ), Th.IsDiscriminantTwelfthRootOfIdealLattice H ⊤ δ ∧ L.lattice.toAddSubgroup = Th.lamOf H ⊤ δ ∧ Th.IsTwoTorsionPointUnkilled H (Th.lamOf H ⊤ δ) (ω₀ / 2) := by
  first | exact @GlobalTheory.Mem.Col2.exists_curve_lattice | exact GlobalTheory.Mem.Col2.exists_curve_lattice | (intros; apply GlobalTheory.Mem.Col2.exists_curve_lattice <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

theorem tup_sgHC_eq {R : Ranks} (P : HCParam R) (i : Fin (R.N R.m - 1)) :
    Formalism.L2.Forms.sgHC R P i = (RowPar.of P).sgHC i := by
  have hi := i.2
  have hN : R.N R.m = (R.k + R.m) + R.m * R.t := N_eq_blocks R R.m
  unfold Formalism.L2.Forms.sgHC RowPar.sgHC
  congr 1
  by_cases h1 : (i : ℕ) < R.k - 1
  · rw [dite_eq_left h1, dite_eq_left h1]
    rfl
  · rw [dite_eq_right h1, dite_eq_right h1]
    have h2 : ((i : ℕ) - (R.k - 1)) / (R.t + 1) < R.m := by
      rw [Nat.div_lt_iff_lt_mul (Nat.succ_pos _)]
      have := R.two_le_m
      have e : R.m * (R.t + 1) = R.m + R.m * R.t := by ring
      have e' : R.m * R.t.succ = R.m * (R.t + 1) := rfl
      omega
    rw [dite_eq_left h2]
    split_ifs with h3
    · simp [RowPar.bAt, h2]
      rfl
    · simp [RowPar.eAt, h2]
      rfl

theorem tup_rowPar_eq (B : Base) (u : B.Word) (τ : Tau B.R) : RowPar.of (B.hcW u τ) = RowPar.of (B.hc τ) := by
  unfold RowPar.of
  rw [B.hcW_v, B.hcW_b, B.hcW_e]

theorem fm_sg_eq : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), ∀ τ (i : Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1)), (((I.fm l u a).sg τ).w i : ℚ) = Formalism.L2.Forms.sgHC (I.rec7 l Z).R ((I.rec7 l Z).hcW u τ) i - rhoVec ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1) i := by
  intro B X I hI hP l Z u a τ i
  have h2 := (tup_sgHC_eq (B.hcW u τ) i).trans (congrArg (fun P => RowPar.sgHC P i) (tup_rowPar_eq B u τ))
  exact (RowPar.sg_eq (B.hc τ) i).trans (congrArg (· - _) h2.symm)

end GlobalTheory.Mem.Col2.TC

end
end

section

noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Col2.ClsZero

section Canon
variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} (Λ : LevFam X.E X.K n SG)

def canon (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) :=
  Classical.epsilon (p := fun d' => ∃ (γ : UF X.E n) (k : Λ.grp),
    d' = ((γ, (k.1 : GLG (E := X.E) (n := n) (SG := SG))) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) • d) (h := ⟨d⟩)

theorem canon_spec (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) : ∃ (γ : UF X.E n) (k : Λ.grp),
    canon Λ d = ((γ, (k.1 : GLG (E := X.E) (n := n) (SG := SG))) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) • d :=
  Classical.epsilon_spec (p := fun d' => ∃ (γ : UF X.E n) (k : Λ.grp), d' = ((γ, (k.1 : GLG (E := X.E) (n := n) (SG := SG))) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) • d)
    ⟨d, 1, 1, (one_smul _ d).symm⟩

theorem canon_smul (γ : UF X.E n) (k : Λ.grp) (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) :
    canon Λ (((γ, (k.1 : GLG (E := X.E) (n := n) (SG := SG))) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) • d) = canon Λ d := by
  unfold canon
  congr 1
  funext d'
  apply propext
  constructor
  · rintro ⟨γ', k', rfl⟩
    exact ⟨γ' * γ, k' * k, by rw [← mul_smul]; rfl⟩
  · rintro ⟨γ', k', rfl⟩
    refine ⟨γ' * γ⁻¹, k' * k⁻¹, ?_⟩
    rw [← mul_smul]
    congr 1
    ext1 <;> simp

theorem canon_idem (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) : canon Λ (canon Λ d) = canon Λ d := by
  obtain ⟨γ, k, h⟩ := canon_spec Λ d
  conv_lhs => rw [h]
  exact canon_smul Λ γ k d

theorem orb_iff (y : Ys X n) (Λ' : LevFam X.E X.K n SG) (hΛ : Λ' = Λ) (Θ : LevQFam X.E X.K n Q) (hΘ : Θ = LevQFam.top X.E X.K n Q)
    (hy : y = Ys.triv X n) (p p' : PtY ST SG Q y) :
    (letI := ptYAct (ST := ST) y Λ' Θ; ∃ g : FrmG Λ' Θ, g • p = p') ↔ canon Λ p'.1.1.deco = canon Λ p.1.1.deco := by
  subst hΛ hΘ hy
  constructor
  · rintro ⟨g, rfl⟩
    exact canon_smul Λ' g.1 g.2.1 p.1.1.deco
  · intro h
    obtain ⟨γ₁, k₁, h₁⟩ := canon_spec Λ' p.1.1.deco
    obtain ⟨γ₂, k₂, h₂⟩ := canon_spec Λ' p'.1.1.deco
    have e : p'.1.1.deco = (((γ₂⁻¹ * γ₁ : UF X.E n), ((k₂⁻¹ * k₁ : Λ'.grp).1 : GLG (E := X.E) (n := n) (SG := SG))) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) • p.1.1.deco := by
      have := h₂.symm.trans (h.trans h₁)
      rw [← eq_inv_smul_iff, ← mul_smul] at this
      exact this
    generalize γ₂⁻¹ * γ₁ = γ at e
    generalize k₂⁻¹ * k₁ = k at e
    let q : DecoF X.E n ST SG Q := ((γ, k.1, 1) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) • p.1.1
    have hq : q.deco = p'.1.1.deco := e.symm
    have hc : ∀ P : Q, (p'.1.1.fr P)⁻¹ * q.fr P ∈ GLint X.E n P.1 := by
      intro P x
      have h1 := q.2 P x
      have h2 := p'.1.1.2 P ((p'.1.1.fr P)⁻¹ (q.fr P x))
      have h3 : p'.1.1.1.2 P ((p'.1.1.fr P)⁻¹ (q.fr P x)) = q.fr P x := LinearEquiv.apply_symm_apply _ _
      rw [h3] at h2
      have h4 : q.1.1 = p'.1.1.1.1 := hq
      rw [h4] at h1
      exact h2.symm.trans h1
    refine ⟨(γ, k, ⟨fun P => ⟨_, hc P⟩, fun _ _ => trivial⟩), ?_⟩
    refine Subtype.ext (Prod.ext (Subtype.ext (Prod.ext e.symm ?_)) ?_)
    · funext P
      show γ.1 * p.1.1.fr P * ((p'.1.1.fr P)⁻¹ * (γ.1 * p.1.1.fr P * ((1 : GLQ X.E n Q) P)⁻¹.1))⁻¹ = p'.1.1.fr P
      simp only [Pi.one_apply, inv_one, OneMemClass.coe_one, mul_one]
      group
    · have h1 : p.1.2 = ∅ := p.2
      have h2 : p'.1.2 = ∅ := p'.2
      show (fun v => γ.1 v) '' p.1.2 = p'.1.2
      rw [h1, h2, Set.image_empty]

theorem eps_eq (y : Ys X n) (Λ' : LevFam X.E X.K n SG) (hΛ : Λ' = Λ) (Θ : LevQFam X.E X.K n Q) (p : PtY ST SG Q y) :
    (letI := ptYAct (ST := ST) y Λ' Θ
     Classical.epsilon (p := fun r => ∃ g : FrmG Λ' Θ, r = (g • p).1.1.deco) (h := ⟨p.1.1.deco⟩)) = canon Λ p.1.1.deco := by
  subst hΛ
  unfold canon
  congr 1
  funext r
  apply propext
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g.1, g.2.1, rfl⟩
  · rintro ⟨γ, k, rfl⟩
    exact ⟨(γ, k, 1), rfl⟩

end Canon

attribute [local instance] starE
variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem levelTypePrimes_stepZero_eq_colLev (h : I.Ok) (a : I.ι) (b : Idx I.sel (I.tup a) (I.idx a) 0) :
    levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 b = colLev I.Ch 0 := by
  obtain ⟨_ | b, hb⟩ := b
  · exact absurd (hb.2 (by have := B.R.two_le_m; omega)) (by simp)
  · exact (h.idx_ok a).zero_G b

theorem chartIndexLevelTwistPrimes_stepZero_eq_top (h : I.Ok) (a : I.ι) (b : Idx I.sel (I.tup a) (I.idx a) 0) :
    levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 b = LevQFam.top _ _ _ _ := by
  obtain ⟨_ | b, hb⟩ := b
  · exact absurd (hb.2 (by have := B.R.two_le_m; omega)) (by simp)
  · exact (h.idx_ok a).zero_Q b

theorem ys0 (a : I.ι) : ysAt B.R I.sel (I.tup a) (I.cst a) 0 = Ys.triv _ _ :=
  if_neg (by have := B.R.two_le_m; omega)

theorem stepZero_chartIndex_subsingleton (h : I.Ok) (a : I.ι) (b b' : Idx I.sel (I.tup a) (I.idx a) 0) : b = b' := by
  have hm : 0 < B.R.m := by have := B.R.two_le_m; omega
  obtain ⟨b0, hb0⟩ := (h.idx_ok a).zero_uniq
  obtain ⟨_ | b, hb⟩ := b
  · exact absurd (hb.2 hm) (by simp)
  obtain ⟨_ | b', hb'⟩ := b'
  · exact absurd (hb'.2 hm) (by simp)
  obtain rfl : b = b' := (hb0 b).trans (hb0 b').symm
  rfl

theorem stepZero_chartIndex_nonempty (h : I.Ok) (a : I.ι) : Nonempty (Idx I.sel (I.tup a) (I.idx a) 0) := by
  obtain ⟨b0, -⟩ := (h.idx_ok a).zero_uniq
  exact ⟨⟨some b0, by have := B.R.two_le_m; simp; omega⟩⟩

theorem cl_eq_iff (h : I.Ok) (u : B.Word) (a : I.ι) (b b' : Idx I.sel (I.tup a) (I.idx a) 0) (p p' : PtAt B.R I.sel (I.tup a) (I.cst a) u 0) :
    (I.stp u a 0).cl b p = (I.stp u a 0).cl b' p' ↔ canon (colLev I.Ch 0) p.1.1.deco = canon (colLev I.Ch 0) p'.1.1.deco := by
  obtain rfl := stepZero_chartIndex_subsingleton h a b b'
  rw [← orb_iff (colLev I.Ch 0) _ _ (levelTypePrimes_stepZero_eq_colLev h a b) _ (chartIndexLevelTwistPrimes_stepZero_eq_top h a b) (ys0 a) p' p]
  constructor
  · intro e
    exact Quotient.exact (eq_of_heq (Sigma.mk.inj e).2)
  · intro e
    exact congrArg (Sigma.mk b) (Quotient.sound e)

theorem cl_rep {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} (S : GStep E K n) (c : S.Cl) : S.cl c.1 (S.rep c) = c :=
  congrArg (Sigma.mk c.1) (S.rp_spec c.1 c.2)

theorem bij0 (h : I.Ok) (u : B.Word) (a : I.ι) (b) : Function.Bijective (I.cl0 u a b) := by
  constructor
  · intro c c' e
    have e1 := (cl_eq_iff h u a b b _ _).1 e
    rw [← cl_rep _ c, ← cl_rep _ c']
    exact (cl_eq_iff h u I.mu0 _ _ _ _).2 e1
  · intro c
    obtain ⟨b0⟩ := stepZero_chartIndex_nonempty h I.mu0
    refine ⟨(I.stp u I.mu0 0).cl b0 (I.pt0 u a I.mu0 ((I.stp u a 0).rep c)), ?_⟩
    have e := (cl_eq_iff h u I.mu0 _ _ _ _).1 (cl_rep _ ((I.stp u I.mu0 0).cl b0 (I.pt0 u a I.mu0 ((I.stp u a 0).rep c))))
    refine Eq.trans ?_ (cl_rep _ c)
    exact (cl_eq_iff h u a _ _ _ _).2 e

theorem stepZero_preferred_iff_canonicalRep (h : I.Ok) (u : B.Word) (a : I.ι) (b : Idx I.sel (I.tup a) (I.idx a) 0)
    (p : PtAt B.R I.sel (I.tup a) (I.cst a) u 0) :
    I.pref u a 0 b p ↔ p.1.1.deco = canon (colLev I.Ch 0) p.1.1.deco := by
  have hm := B.R.two_le_m
  have e := eps_eq (ST := (B.primes X).vT u) (colLev I.Ch 0) _ _ (levelTypePrimes_stepZero_eq_colLev h a b)
    (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 b) p
  constructor
  · intro hp
    exact Eq.trans (hp.1 rfl) e
  · intro hp
    exact ⟨fun _ => hp.trans e.symm, fun e' => absurd e' (by omega),
      topLev_pref_ne I.Ch I.sel (I.tup a) (I.cst a) I.Ps u (by omega) _⟩

theorem empty_mem_couplingIndexAtStep_zero (a : I.ι) (N) : ∅ ∈ (ysAt B.R I.sel (I.tup a) (I.cst a) 0).ys N := by
  rw [ys0]; rfl

theorem stepZero_representative_deco_eq_canonical (h : I.Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) :
    ((I.stp u a 0).rep c).1.1.deco = canon (colLev I.Ch 0) ((I.stp u a 0).rep c).1.1.deco := by
  obtain ⟨b, q⟩ := c
  let p := (I.stp u a 0).rep ⟨b, q⟩
  obtain ⟨γ, k, e⟩ := canon_spec (colLev I.Ch 0) p.1.1.deco
  let p' : PtAt B.R I.sel (I.tup a) (I.cst a) u 0 := ⟨(((γ, k.1, 1) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs) × GLQ B.fields.E (B.R.N 0) (I.Q a)) • p.1.1, ∅), empty_mem_couplingIndexAtStep_zero a _⟩
  have e' : p'.1.1.deco = canon (colLev I.Ch 0) p.1.1.deco := e.symm
  have hc : (I.stp u a 0).cl b p' = ⟨b, q⟩ := by
    refine Eq.trans ?_ (cl_rep _ ⟨b, q⟩)
    refine (cl_eq_iff h u a b b _ _).2 ?_
    rw [e', canon_idem]
  have hp := @pref_prefRep _ _ _ ((I.stp0 u a 0).actD b) (I.pref u a 0 b) p'
    ((stepZero_preferred_iff_canonicalRep h u a b p').2 (by rw [e', canon_idem]))
  have hq : q = Quotient.mk _ p' := (eq_of_heq (Sigma.mk.inj hc).2).symm
  refine (stepZero_preferred_iff_canonicalRep h u a b _).1 ?_
  rw [hq]
  exact hp

theorem stepZero_corresponding_representatives_same_deco (h : I.Ok) (u : B.Word) (a : I.ι) (b) (c : (I.stp u I.mu0 0).Cl) :
    ((I.stp u a 0).rep (I.cl0 u a b c)).1.1.deco = ((I.stp u I.mu0 0).rep c).1.1.deco := by
  refine (stepZero_representative_deco_eq_canonical h u a _).trans (Eq.trans ?_ (stepZero_representative_deco_eq_canonical h u I.mu0 c).symm)
  exact (cl_eq_iff h u a (I.cl0 u a b c).1 b ((I.stp u a 0).rep (I.cl0 u a b c))
    (I.pt0 u I.mu0 a ((I.stp u I.mu0 0).rep c))).1 (cl_rep (I.stp u a 0) (I.cl0 u a b c))

theorem stepZero_classes_bijective_same_deco : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ u a b,
    Function.Bijective (I.cl0 u a b) ∧
      ∀ c, ((I.stp u a 0).rep (I.cl0 u a b c)).1.1.deco = ((I.stp u I.mu0 0).rep c).1.1.deco :=
  fun _ h u a b => ⟨bij0 h u a b, stepZero_corresponding_representatives_same_deco h u a b⟩

end GlobalTheory.Mem.Col2.ClsZero

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2

theorem cosetIn_congr : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ} (p p' : PtAt R sel mu cst u j), p.1.2 = p'.1.2 → p.1.1.fr = p'.1.1.fr → (∀ w : Pr.vGs, localization₂ w.1.asIdeal p.1.1.deco.1.N = localization₂ w.1.asIdeal p'.1.1.deco.1.N ∧ p.1.1.deco.1.be w = p'.1.1.deco.1.be w) → cosetIn p = cosetIn p' := by
  intro X Pr R sel S mu cst u j p p' h2 hfr hloc
  have hF : ∀ P, frsF sel mu p.1.1 P = frsF sel mu p'.1.1 P := by
    intro P
    unfold frsF
    split_ifs with h
    · have e1 := (hloc ⟨P.1, h⟩).1
      have e2 := (hloc ⟨P.1, h⟩).2
      unfold Deco.liftFr Deco.at
      rw [e1, e2]
    · rw [hfr]
  funext P
  unfold cosetIn
  rw [h2, hF P]

end GlobalTheory.Mem.Col2
end
