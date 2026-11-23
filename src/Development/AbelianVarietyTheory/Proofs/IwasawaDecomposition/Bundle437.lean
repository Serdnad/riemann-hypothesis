module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle416
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StepZeroTwistReferenceTupleEqId
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle375
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle271
import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle419
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle010
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RightTranslationActionApply
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteDetermining
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle421
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle368
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle423
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
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.RowDeco

open GlobalTheory.Mem.R3.RowAd

variable (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px)

theorem gram_X'_eq_one (hI : I.Ok) : X.toD7.sp.X'.gram = 1 := by
  obtain ⟨hs, -, h2, -⟩ := hI.spaces
  change X.B.sp.X'.gram = 1
  rw [h2]
  refine Matrix.ext fun i i' => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ i i').trans ?_
  simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]

theorem ptE_mul (h k : Bridge.Gf X.toD7.sp.X') : ptE X (h * k) = ptE X h * ptE X k := by
  unfold ptE
  rw [Subgroup.coe_mul, map_mul, map_mul]
  rfl

theorem ptE_finHom (g : GA X.toD7 X.toD7.sp.X') :
    ptE X ⟨finHom X.toD7.sp.X' g, g, rfl⟩ = ColAd.finN X.toD7.sp.X' (rank_X' X) g := by
  apply Units.ext
  ext i j
  rw [ColAd.finN_apply]
  rfl

theorem ptE_mem_UAd (hI : I.Ok) (h : Bridge.Gf X.toD7.sp.X') :
    ptE X h ∈ Formalism.L2.Col.UAd X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) := by
  obtain ⟨g, hg⟩ := h.2
  have e : h = ⟨finHom X.toD7.sp.X' g, g, rfl⟩ := Subtype.ext hg.symm
  rw [e, ptE_finHom]
  exact ColAd.finN_mem (rank_X' X) (gram_X'_eq_one X I hI) g

end GlobalTheory.Mem.R3.RowDeco

noncomputable section
namespace GlobalTheory.Mem.R3.RowDeco
open GlobalTheory.Mem.R3.RowAd
variable (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px)

theorem decoAd_mul (hI : I.Ok) {U : Set I.ι} (t : TupU I U) (h q : Bridge.Gf X.toD7.sp.X')
    (hz : ptE X q ∈ Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅) :
    decoAd X I t (h * q) =
      ((1 : Formalism.L2.Col.UF X.B.fields.E (X.B.R.N X.B.R.m - 1)),
        ((Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ⟨ptE X q, hz⟩)⁻¹ :
          Formalism.L2.Col.GLG (E := X.B.fields.E) (n := X.B.R.N X.B.R.m - 1) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1))) •
        decoAd X I t h := by
  have hh := ptE_mem_UAd X I hI h
  have hq := ptE_mem_UAd X I hI q
  unfold decoAd Formalism.L2.Col.decoOf
  rw [ptE_mul]
  split_ifs with h1 h2 h2
  · apply Subtype.ext
    rw [Formalism.L2.Col.DecoSet.smul_val]
    exact ColAd.LevGrp.decoRaw_mul_levelIwahori_reduction X.toD7.sp.cm (ptE X h) (ptE X q) hz
  · exact absurd (Formalism.L2.Col.decorated_lattice_exists X.toD7.sp.cm _ _ _ _ hh) h2
  · exact absurd (Formalism.L2.Col.decorated_lattice_exists X.toD7.sp.cm _ _ _ _ (mul_mem hh hq)) h1
  · exact absurd (Formalism.L2.Col.decorated_lattice_exists X.toD7.sp.cm _ _ _ _ (mul_mem hh hq)) h1

end GlobalTheory.Mem.R3.RowDeco

noncomputable section
namespace GlobalTheory.Mem.R3.RowDeco
open GlobalTheory.Mem.R3.RowAd
variable (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px)

theorem reindex_mem_St_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {a b : ℕ} (e : Fin a ≃ Fin b)
    {x : GL (Fin a) (E ⊗[F] Formalism.L2.Herm.Af F)} (hx : x ∈ Formalism.L2.DIV.St (1 : GL (Fin a) (E ⊗[F] Formalism.L2.Herm.Af F))) :
    Units.map (Matrix.reindexAlgEquiv (E ⊗[F] Formalism.L2.Herm.Af F) (E ⊗[F] Formalism.L2.Herm.Af F) e).toMonoidHom x ∈ Formalism.L2.DIV.St (1 : GL (Fin b) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨Units.map (Matrix.reindexAlgEquiv (Formalism.L2.Herm.intAf F E) (Formalism.L2.Herm.intAf F E) e).toMonoidHom y, ?_⟩
  apply Units.ext
  ext i j
  simp [Formalism.L2.DIV.frGL, Formalism.L2.DIV.intGL]
  rfl

end GlobalTheory.Mem.R3.RowDeco

namespace GlobalTheory.Mem.R3.RowDeco
open GlobalTheory.Mem.R3.RowAd
variable (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px)

theorem unitaryFiniteAdelicPointAsMatrix_mem_flagIwahori (hI : I.Ok) {U : Set I.ι} (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hL : LevOf X I U L) (t : TupU I U)
    (q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q) :
    ptE X (q : Bridge.Gf X.toD7.sp.X') ∈ Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ := by
  refine ⟨⟨ptE_mem_UAd X I hI _, ?_⟩, ?_⟩
  · have hSt := Formalism.L2.DIV.parLev_St (RowAct.parLev_of_Q X.toD7.sp.X' L.βX (L.datXt t) q)
    have e : Formalism.L2.DIV.St L.βX = Formalism.L2.DIV.St 1 := by rw [hL.beta.2]
    rw [e] at hSt
    exact reindex_mem_St_one _ hSt
  · refine Subgroup.mem_iInf.2 fun P => Subgroup.mem_iInf.2 fun hP => ?_
    exact absurd hP (Finset.notMem_empty _)

end GlobalTheory.Mem.R3.RowDeco

namespace GlobalTheory.Mem.R3.RowDeco
open GlobalTheory.Mem.R3.RowAd

theorem redAt_reindex {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {a b : ℕ} (e : Fin a ≃ Fin b)
    (β : GL (Fin a) (E ⊗[F] Formalism.L2.Herm.Af F)) (hβ : β = 1)
    (x : GL (Fin a) (E ⊗[F] Formalism.L2.Herm.Af F)) (hx : x ∈ Formalism.L2.DIV.St β)
    (hx' : Units.map (Matrix.reindexAlgEquiv (E ⊗[F] Formalism.L2.Herm.Af F) (E ⊗[F] Formalism.L2.Herm.Af F) e).toMonoidHom x ∈
      Formalism.L2.DIV.St (1 : GL (Fin b) (E ⊗[F] Formalism.L2.Herm.Af F))) (PP : Formalism.L2.DIV.Pl E) :
    Formalism.L2.DIV.redAt 1 PP ⟨_, hx'⟩ =
      Units.map (Matrix.reindexAlgEquiv (Formalism.L2.DIV.kP PP) (Formalism.L2.DIV.kP PP) e).toMonoidHom (Formalism.L2.DIV.redFn β PP x) := by
  subst hβ
  obtain ⟨y, rfl⟩ := hx
  have hy : Units.map (Matrix.reindexAlgEquiv (E ⊗[F] Formalism.L2.Herm.Af F) (E ⊗[F] Formalism.L2.Herm.Af F) e).toMonoidHom
      (Formalism.L2.DIV.frGL 1 y) =
      Formalism.L2.DIV.frGL 1 (Units.map (Matrix.reindexAlgEquiv (Formalism.L2.Herm.intAf F E) (Formalism.L2.Herm.intAf F E) e).toMonoidHom y) := by
    apply Units.ext
    ext i j
    simp [Formalism.L2.DIV.frGL, Formalism.L2.DIV.intGL]
    rfl
  have hred : ∀ (z : GL (Fin b) (E ⊗[F] Formalism.L2.Herm.Af F)) (hz : z ∈ Formalism.L2.DIV.St 1)
      (y' : GL (Fin b) (Formalism.L2.Herm.intAf F E)) (hzy : Formalism.L2.DIV.frGL 1 y' = z),
      Formalism.L2.DIV.redAt 1 PP ⟨z, hz⟩ = Formalism.UG.bc (Formalism.L2.DIV.resS F PP) y' := by
    intro z hz y' hzy
    subst hzy
    exact congrArg (Formalism.UG.bc (Formalism.L2.DIV.resS F PP)) (Formalism.L2.DIV.pullFr_frGL 1 y')
  rw [hred _ hx' _ hy.symm, Formalism.L2.DIV.redFn_frGL]
  apply Units.ext
  ext i j
  rfl

variable (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px)

theorem redG_ptE {U : Set I.ι} (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hL : LevOf X I U L) (t : TupU I U)
    (q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q)
    (hz : ptE X (q : Bridge.Gf X.toD7.sp.X') ∈ Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅)
    (w : Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) :
    Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ⟨_, hz⟩ w =
      Units.map (Matrix.reindexAlgEquiv (Formalism.L2.DIV.kP w.1) (Formalism.L2.DIV.kP w.1) (finCongr (rank_X' X))).toMonoidHom
        (Formalism.L2.DIV.redFn L.βX w.1 (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _))) :=
  redAt_reindex (finCongr (rank_X' X)) L.βX hL.beta.2 _
    (Formalism.L2.DIV.parLev_St (RowAct.parLev_of_Q X.toD7.sp.X' L.βX (L.datXt t) q)) (Formalism.L2.Col.congruence_subgroup_le_stabilizer _ _ _ hz) w.1

end GlobalTheory.Mem.R3.RowDeco
end
end
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3
open scoped ComplexOrder

namespace GlobalTheory.Mem.ColTie

section Lin

variable {K M : Type} [Field K] [AddCommGroup M] [Module ℂ M] {σ : K →+* ℂ} {n : ℕ}

theorem eq_sum_single (x : Fin n → K) : x = ∑ i, x i • (Pi.single i (1 : K) : Fin n → K) := by
  ext k
  simp [Finset.sum_apply, Pi.single_apply]

theorem mem_span_single (j : (Fin n → K) →ₛₗ[σ] M) (x : Fin n → K) :
    j x ∈ Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) := by

  rw [eq_sum_single x, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem span_single_eq (j : (Fin n → K) →ₛₗ[σ] M) :
    Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = Submodule.span ℂ (Set.range j) := by
  refine le_antisymm (Submodule.span_mono ?_) ?_
  · rintro _ ⟨i, rfl⟩
    exact ⟨_, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact mem_span_single j x

theorem exists_equiv_of_bases {M' : Type} [AddCommGroup M'] [Module ℂ M'] (j : (Fin n → K) →ₛₗ[σ] M)
    (j' : (Fin n → K) →ₛₗ[σ] M') (hli : LinearIndependent ℂ fun i => j (Pi.single i 1))
    (hsp : Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = ⊤)
    (hli' : LinearIndependent ℂ fun i => j' (Pi.single i 1))
    (hsp' : Submodule.span ℂ (Set.range fun i => j' (Pi.single i 1)) = ⊤) :
    ∃ e : M ≃ₗ[ℂ] M', ∀ x, e (j x) = j' x := by
  let b := Module.Basis.mk hli hsp.ge
  let b' := Module.Basis.mk hli' hsp'.ge
  refine ⟨b.equiv b' (Equiv.refl _), fun x => ?_⟩

  rw [eq_sum_single x, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smulₛₗ j, map_smulₛₗ j', LinearEquiv.map_smul]
  congr 1
  have h1 : j (Pi.single i 1) = b i := (Module.Basis.mk_apply hli hsp.ge i).symm
  have h2 : j' (Pi.single i 1) = b' i := (Module.Basis.mk_apply hli' hsp'.ge i).symm
  rw [h1, h2, Module.Basis.equiv_apply, Equiv.refl_apply]

end Lin

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (hX : X.Ok)

def ipLev (z z' : MtildeV W Ch sel mu P) : X.K :=
  (mtildeGSD W Ch sel mu P).ip (mtildeOk W Ch sel mu hX P) z.1 z'.1

def ipK (z z' : MtildeV W Ch sel mu P) : X.K :=
  (mtildeKGSD W Ch sel mu).ip (mtildeKOk W Ch sel mu hX) z.1 z'.1

theorem li_zOf : LinearIndependent X.K fun i => zOf W Ch sel mu P hX (Pi.single i 1) := by
  have h := (Pi.basisFun X.K (Fin (dimP W Ch sel mu P hX))).linearIndependent.map' (zOf W Ch sel mu P hX)
    (LinearMap.ker_eq_bot.2 (zOf_injective W Ch sel mu P hX))
  simpa [Function.comp_def] using h

def jP (σ : X.K →+* ℂ) : (Fin (dimP W Ch sel mu P hX) → X.K) →ₛₗ[σ] MtP W Ch sel mu P σ :=
  (toMtP W Ch sel mu P σ).comp (zOf W Ch sel mu P hX)

theorem linearIndependent_jP_single (σ : X.K →+* ℂ) : LinearIndependent ℂ fun i => jP W Ch sel mu P hX σ (Pi.single i 1) :=
  toMtilde_linearIndependent W Ch sel mu P σ (li_zOf W Ch sel mu P hX)

theorem span_range_jP_single_eq_top (σ : X.K →+* ℂ) : Submodule.span ℂ (Set.range fun i => jP W Ch sel mu P hX σ (Pi.single i 1)) = ⊤ := by
  refine eq_top_iff.2 ?_
  rw [← toMtilde_span W Ch sel mu P σ hX, Submodule.span_le]
  rintro _ ⟨z, rfl⟩
  obtain ⟨x, rfl⟩ := zOf_surjective W Ch sel mu P hX z
  exact mem_span_single (jP W Ch sel mu P hX σ) x

end Gen

section TC

attribute [local instance] starE

def sig (B : Base) : B.fields.K →+* ℂ := B.embLL

end TC

end GlobalTheory.Mem.ColTie
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.ChEx

section Pt

open Classical

variable {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}

theorem ptAt_cosetG (q : PtAt R sel mu cst u j) (h : j + 1 = R.m) :
    ∃ y : Sp X.E (R.N j), (∀ w ∈ Pr.vGs, ((qOf w : ℕ) : X.E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N) ∧ y ∈ q.1.2 ∧
      ∀ z ∈ q.1.2, ∀ w ∈ Pr.vGs, z - y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N := by
  obtain ⟨y, hy, hY⟩ := q.mem_ybSet h
  refine ⟨y, fun w hw => ?_, ?_, fun z hz w hw => ?_⟩
  · have := (Formalism.L2.Col.mem_locLat _ _ _ _).1 hy ⟨w, Finset.mem_union_left _ hw⟩
    simpa [hw] using this
  · rw [hY, Set.mem_setOf_eq, sub_self]
    exact zero_mem _
  · rw [hY, Set.mem_setOf_eq, Formalism.L2.Col.mem_locLat] at hz
    simpa [hw] using hz ⟨w, Finset.mem_union_left _ hw⟩

theorem cosetIn_eqG (q : PtAt R sel mu cst u j) {y : Sp X.E (R.N j)} (hy0 : y ∈ q.1.2)
    (hY : ∀ z ∈ q.1.2, ∀ w ∈ Pr.vGs, z - y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) :
    cosetIn q P = {z | z - (q.1.1.deco.1.liftFr ⟨P.1, hP⟩).symm y ∈ stdAt X.E (R.N j) P.1} := by
  have hf := GlobalTheory.TopStep.liftFr_spec q.1.1.deco.2 ⟨P.1, hP⟩
  have hfr : frsF sel mu q.1.1 P = q.1.1.deco.1.liftFr ⟨P.1, hP⟩ := by
    unfold frsF
    rw [dite_eq_left hP]
  ext z
  simp only [cosetIn, Set.mem_setOf_eq, if_pos hP, pow_zero, inv_one, one_smul, hfr]
  constructor
  · rintro ⟨y', hy', hz⟩
    have h1 : (q.1.1.deco.1.liftFr ⟨P.1, hP⟩).symm y' - (q.1.1.deco.1.liftFr ⟨P.1, hP⟩).symm y ∈ stdAt X.E (R.N j) P.1 := by
      rw [← map_sub]
      exact (hf.1 _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hY y' hy' P.1 hP)
    have := add_mem hz h1
    rwa [sub_add_sub_cancel] at this
  · intro hz
    exact ⟨y, hy0, hz⟩

theorem bar_eqG (q : PtAt R sel mu cst u j) {y : Sp X.E (R.N j)}
    (hy : ∀ w ∈ Pr.vGs, ((qOf w : ℕ) : X.E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N) (hy0 : y ∈ q.1.2)
    (hY : ∀ z ∈ q.1.2, ∀ w ∈ Pr.vGs, z - y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N) (w : Pr.vGs) :
    bar q w = {redV w.1 (((qOf w.1 : ℕ) : X.E) • (q.1.1.deco.1.liftFr w).symm y)} := by
  have hd := q.1.1.deco.2
  have hf := GlobalTheory.TopStep.liftFr_spec hd w
  have hq := hy w.1 w.2
  have key : q.1.1.deco.1.be w (((qOf w.1 : ℕ) : X.E) • y) =
      redV w.1 (((qOf w.1 : ℕ) : X.E) • (q.1.1.deco.1.liftFr w).symm y) := by
    rw [← map_smul]
    have hs : (q.1.1.deco.1.liftFr w).symm (((qOf w.1 : ℕ) : X.E) • y) ∈ stdAt X.E _ w.1 :=
      (hf.1 _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hq)
    rw [← hf.2 _ hs, LinearEquiv.apply_symm_apply]
  ext v
  simp only [bar, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← key]
    have ht : z - y ∈ q.1.1.deco.1.at w.1 := hY z hz w.1 w.2
    have e : ((qOf w.1 : ℕ) : X.E) • z = ((qOf w.1 : ℕ) : X.E) • y + ((qOf w.1 : ℕ) : X.E) • (z - y) := by
      rw [← smul_add, add_sub_cancel]
    rw [e, hd.be_add w _ hq _ (GlobalTheory.TopStep.smul_mem_locP (GlobalTheory.TopStep.intAt_nat _) ht),
      GlobalTheory.TopStep.be_smul_int hd w (GlobalTheory.TopStep.intAt_nat _) ht, GlobalTheory.TopStep.reduction_absNorm_eq_zero, zero_smul, add_zero]
  · rintro rfl
    exact ⟨y, hy0, key.symm⟩

theorem cosetIn_eq_iff_bar_cq : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ},
    (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) →
    ∀ (r r' : PtAt R sel mu cst u j), cosetIn r = cosetIn r' ↔ bar r = bar r' ∧ GlobalTheory.Mem.Col2.ChEx.cqOf r = GlobalTheory.Mem.Col2.ChEx.cqOf r' := by
  intro X Pr R sel S mu cst u j _ hq q q'
  by_cases h : j + 1 = R.m
  · obtain ⟨y, hy, hy0, hY⟩ := ptAt_cosetG q h
    obtain ⟨y', hy', hy0', hY'⟩ := ptAt_cosetG q' h
    have hA : ∀ (p : PtAt R sel mu cst u j) (y : Sp X.E (R.N j)),
        (∀ w ∈ Pr.vGs, ((qOf w : ℕ) : X.E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal p.1.1.deco.1.N) → ∀ w : Pr.vGs,
        ((qOf w.1 : ℕ) : X.E) • (p.1.1.deco.1.liftFr w).symm y ∈ stdAt X.E (R.N j) w.1 := by
      intro p y hy w
      have hf := GlobalTheory.TopStep.liftFr_spec p.1.1.deco.2 w
      rw [← map_smul]
      exact (hf.1 _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hy w.1 w.2)
    constructor
    · intro H
      refine ⟨funext fun w => ?_, funext fun P => ?_⟩
      · have := congrFun H ⟨w.1, Finset.mem_union_left _ w.2⟩
        rw [cosetIn_eqG q hy0 hY _ w.2, cosetIn_eqG q' hy0' hY' _ w.2] at this
        rw [bar_eqG q hy hy0 hY, bar_eqG q' hy' hy0' hY', Set.singleton_eq_singleton_iff]
        exact (coset_eq_iff_redV (hq w.1 w.2) (hA q y hy w) (hA q' y' hy' w)).1 this
      · unfold cqOf
        rw [H]
    · rintro ⟨H1, H2⟩
      funext P
      by_cases hP : P.1 ∈ Pr.vGs
      · have := congrFun H1 ⟨P.1, hP⟩
        rw [bar_eqG q hy hy0 hY, bar_eqG q' hy' hy0' hY', Set.singleton_eq_singleton_iff] at this
        rw [cosetIn_eqG q hy0 hY P hP, cosetIn_eqG q' hy0' hY' P hP]
        exact (coset_eq_iff_redV (hq P.1 hP) (hA q y hy ⟨P.1, hP⟩) (hA q' y' hy' ⟨P.1, hP⟩)).2 this
      · have hQ : P.1 ∈ QE sel (mu : Chr X.F X.E X.K) := (Finset.mem_union.mp P.2).resolve_left hP
        have := congrFun H2 ⟨P.1, hQ⟩
        exact this
  · have e : ∀ p : PtAt R sel mu cst u j, p.1.2 = ∅ := fun p => by
      have := p.2
      rw [ysAt_ys_of_ne sel mu cst h] at this
      exact this
    have h1 : ∀ p : PtAt R sel mu cst u j, cosetIn p = fun _ => ∅ := fun p => by
      funext P
      ext z
      simp [cosetIn, e p]
    have h2 : ∀ p : PtAt R sel mu cst u j, bar p = fun _ => ∅ := fun p => by
      funext w
      ext v
      simp [bar, e p]
    have h3 : ∀ p : PtAt R sel mu cst u j, cqOf p = fun _ => ∅ := fun p => by
      funext P
      exact congrFun (h1 p) _
    rw [h1 q, h1 q', h2 q, h2 q', h3 q, h3 q']
    simp

end Pt

end GlobalTheory.Mem.Col2.ChEx
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx


open Classical in
theorem frsF_ya_symm {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
    {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}
    (Λ : LevFam X.E X.K (R.N j) Pr.vGs) (Θ : LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K)))
    (g : FrmG Λ Θ) (r : PtAt R sel mu cst u j) (P : QE sel (mu : Chr X.F X.E X.K)) (hP : P.1 ∉ Pr.vGs) (y : Sp X.E (R.N j)) :
    (frsF sel mu (ya Λ Θ g r).1.1 ⟨P.1, Finset.mem_union_right _ P.2⟩).symm (g.1.1 y) =
      (g.2.2.1 P).1 ((frsF sel mu r.1.1 ⟨P.1, Finset.mem_union_right _ P.2⟩).symm y) := by
  rw [LinearEquiv.symm_apply_eq]
  have e1 : (⟨P.1, (Finset.mem_union.mp (Finset.mem_union_right _ P.2)).resolve_left hP⟩ : QE sel (mu : Chr X.F X.E X.K)) = P :=
    Subtype.ext rfl
  simp only [frsF, dif_neg hP, e1]
  show _ = (g.1.1 * r.1.1.1.2 P * ((g.2.2.1 P)⁻¹).1) ((g.2.2.1 P).1 ((r.1.1.1.2 P).symm y))
  have e2 : ((g.2.2.1 P)⁻¹).1 ((g.2.2.1 P).1 ((r.1.1.1.2 P).symm y)) = (r.1.1.1.2 P).symm y := by
    show (g.2.2.1 P).1.symm ((g.2.2.1 P).1 _) = _
    exact LinearEquiv.symm_apply_apply _ _
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, e2]
  show g.1.1 y = g.1.1 ((r.1.1.1.2 P) ((r.1.1.1.2 P).symm y))
  rw [LinearEquiv.apply_symm_apply]

theorem invActs_cqOf : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → GlobalTheory.Mem.Col2.ChEx.InvActs (GlobalTheory.Mem.Col2.ChEx.cqOf (R := R) (cst := cst) (u := u) (j := j) : PtAt R sel mu cst u j → _) := by
  intro X Pr R sel S mu cst u j hQ Λ Θ g r P
  have hP := hQ P.1 P.2
  ext z
  simp only [cqOf, cosetIn, Set.mem_setOf_eq, Set.mem_image, if_neg hP]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, hz⟩
    refine ⟨(g.2.2.1 P).1.symm z, ⟨y, hy, ?_⟩, LinearEquiv.apply_symm_apply _ _⟩
    rw [frsF_ya_symm Λ Θ g r P hP y] at hz
    rw [← (g.2.2.1 P).2]
    rw [map_smul, map_sub, LinearEquiv.apply_symm_apply]
    exact hz
  · rintro ⟨z0, ⟨y, hy, hz⟩, rfl⟩
    refine ⟨g.1.1 y, ⟨y, hy, rfl⟩, ?_⟩
    rw [frsF_ya_symm Λ Θ g r P hP y, ← map_sub, ← map_smul]
    exact ((g.2.2.1 P).2 _).2 hz

end GlobalTheory.Mem.Col2.ChEx
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isCentralGroupAlgebraIdempotent_universal : ∀ D : D7, EIdem D := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.eIdem_all | exact GlobalTheory.HeightCounting.FormsStep.eIdem_all | (intros; apply GlobalTheory.HeightCounting.FormsStep.eIdem_all <;> assumption)
end
