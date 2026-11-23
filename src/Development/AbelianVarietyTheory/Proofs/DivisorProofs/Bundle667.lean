module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle620
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle629
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Algebra.DirectSum.LinearMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCocycleFirstChernClassTateTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle462
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle624
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle623
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle625
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeC
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.FormsLocus

open GlobalTheory.AbLaw

variable {Rg : Type} [CommRing Rg]

def ringOf {T : Scheme.{0}} {n : ℕ} (g : T ⟶ Sp (MvPolynomial (Fin n) Rg)) :
    MvPolynomial (Fin n) Rg →+* Γ(T, ⊤) :=
  g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv.hom

def cstT {T : Scheme.{0}} (t : T ⟶ Sp Rg) : Rg →+* Γ(T, ⊤) :=
  t.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of Rg)).inv.hom

theorem ringOf_X {T : Scheme.{0}} {n : ℕ} (g : T ⟶ Sp (MvPolynomial (Fin n) Rg)) (k : Fin n) :
    ringOf g (MvPolynomial.X k) = coord g k := rfl

def expand (mA mB : ℕ) (F : MvPolynomial (Fin mB) Rg) :
    MvPolynomial (Fin mA) (MvPolynomial (Fin (mA * mB)) Rg) :=
  MvPolynomial.eval₂ (MvPolynomial.C.comp MvPolynomial.C)
    (fun j => ∑ i, MvPolynomial.C (MvPolynomial.X (finProdFinEquiv (i, j))) * MvPolynomial.X i) F

variable {A₀ : Scheme.{0}} {N : LB A₀} {mA : ℕ}

def monSec (a : Fin mA → LB.Sec N) (d : ℕ) (ν : Fin mA →₀ ℕ) : LB.Sec (GlobalTheory.AbLaw.pw N (d : ℤ)) where
  f := fun q => if ∑ i, ν i = d then ∏ i, ((a i).f q) ^ ν i else 0
  compat := fun (q q' : N.ι) => by
    change (A₀.presheaf.map (homOfLE (inf_le_left : N.U q ⊓ N.U q' ≤ N.U q)).op).hom
        (if ∑ i, ν i = d then ∏ i, ((a i).f q) ^ ν i else 0) =
      ((N.g q q' ^ (d : ℤ) : Γ(A₀, N.U q ⊓ N.U q')ˣ) : Γ(A₀, N.U q ⊓ N.U q')) *
        (A₀.presheaf.map (homOfLE (inf_le_right : N.U q ⊓ N.U q' ≤ N.U q')).op).hom
          (if ∑ i, ν i = d then ∏ i, ((a i).f q') ^ ν i else 0)
    split_ifs with h
    · simp only [map_prod, map_pow]
      simp only [(a _).compat, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h]
      rw [zpow_natCast, Units.val_pow_eq_pow_val]
    · simp only [map_zero, mul_zero]

omit [CommRing Rg] in
theorem idPb {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) :
    IsPullback (𝟙 X) f f (Spec.map (CommRingCat.ofHom (RingHom.id R))) := by
  rw [CommRingCat.ofHom_id, Spec.map_id]
  exact IsPullback.id_horiz f

variable {X : Scheme.{0}} {M : LB X}

def vecOf {f : X ⟶ Sp Rg} (Q : Perf f M) (s : LB.Sec M) : Fin Q.a → Rg :=
  ((Q.sec Rg (RingHom.id Rg) X (𝟙 X) f (idPb f)).choose.symm (finSecPullId s)).1

theorem vecOf_ker {f : X ⟶ Sp Rg} (Q : Perf f M) (s : LB.Sec M) : (Q.D₀.map (RingHom.id Rg)).mulVec (vecOf Q s) = 0 :=
  ((Q.sec Rg (RingHom.id Rg) X (𝟙 X) f (idPb f)).choose.symm (finSecPullId s)).2

theorem vecOf_spec {f : X ⟶ Sp Rg} (Q : Perf f M) (s : LB.Sec M) (i : Q.I) :
    rs X (le_pull M (𝟙 X) (Q.le i)) ((finSecPullId s).f (fun _ => Q.ch i)) =
      ∑ k, cst f ((𝟙 X) ⁻¹ᵁ Q.W i) (vecOf Q s k) * (Scheme.Hom.app (𝟙 X) (Q.W i)).hom (Q.u k i) := by
  have h := (Q.sec Rg (RingHom.id Rg) X (𝟙 X) f (idPb f)).choose_spec
    ((Q.sec Rg (RingHom.id Rg) X (𝟙 X) f (idPb f)).choose.symm (finSecPullId s)) i
  rw [Equiv.apply_symm_apply] at h
  exact h

variable {mB : ℕ} {f : A₀ ⟶ Sp Rg}

def polys (Q : ∀ d : ℕ, Perf f (GlobalTheory.AbLaw.pw N (d : ℤ))) (a : Fin mA → LB.Sec N) (d : ℕ) (F : MvPolynomial (Fin mB) Rg)
    (k : Fin (Q d).a) : MvPolynomial (Fin (mA * mB)) Rg :=
  ∑ ν ∈ (expand mA mB F).support, (expand mA mB F).coeff ν * MvPolynomial.C (vecOf (Q d) (monSec a d ν) k)

def formIdeal (Q : ∀ d : ℕ, Perf f (GlobalTheory.AbLaw.pw N (d : ℤ))) (a : Fin mA → LB.Sec N) {B₀ : Scheme.{0}} {H : LB B₀}
    (fB : B₀ ⟶ Sp Rg) (b : Fin mB → LB.Sec H) : Ideal (MvPolynomial (Fin (mA * mB)) Rg) :=
  Ideal.span {P | ∃ (d : ℕ) (F : MvPolynomial (Fin mB) Rg) (k : Fin (Q d).a),
    F.IsHomogeneous d ∧ Kills fB b F ∧ P = polys Q a d F k}

end GlobalTheory.FormsLocus
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieType

noncomputable section
namespace GlobalTheory.UPel.HT.LieType


open Polynomial in
theorem toLin'_map_aeval_int {F : Type} [Field F] [NumberField F] {g : ℕ}
    (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (x : 𝓞 F) (p : ℤ[X]) :
    Matrix.toLin' (φ (aeval x p)) = aeval (Matrix.toLin' (φ x)) (p.map (algebraMap ℤ ℂ)) := by
  have h1 : φ (aeval x p) = aeval (φ x) p := (Polynomial.aeval_algHom_apply φ.toIntAlgHom x p).symm
  rw [h1, ← Polynomial.aeval_map_algebraMap ℂ (φ x) p]
  exact (Polynomial.aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin g)) (φ x) _).symm


open Polynomial in
theorem trace_eq_sum_finrank_eigSp : ∀ (F : Type) [Field F] [NumberField F] (g : ℕ)
    (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (c : 𝓞 F),
    (φ c).trace = ∑ τ : F →+* ℂ, (Module.finrank ℂ (eigSp φ τ) : ℂ) * τ (c : F) := by
  intro F _ _ g φ c
  classical
  obtain ⟨α, hinj, ⟨f, hf0, hfmap⟩, hmul⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_sepElt (E := F) (F := ℂ)
    (RingHom.id ℂ) (fun τ => τ.comp (algebraMap (𝓞 F) F)) (fun _ _ => rfl)
  simp only [RingHom.comp_apply] at hinj hfmap
  set L : Module.End ℂ (Fin g → ℂ) := Matrix.toLin' (φ α) with hL

  have hLf : aeval L (∏ τ : F →+* ℂ, (X - C (τ ((α : 𝓞 F) : F)))) = 0 := by
    rw [← hfmap, ← algebraMap_int_eq, hL, ← toLin'_map_aeval_int, hf0, map_zero, map_zero]
  have hss : L.IsSemisimple := by
    refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero ?_ hLf
    exact (Polynomial.separable_prod_X_sub_C_iff'.2 fun x _ y _ h => hinj h).squarefree

  have hW : ∀ τ : F →+* ℂ, eigSp φ τ = L.eigenspace (τ ((α : 𝓞 F) : F)) := by
    intro τ
    ext u
    rw [Module.End.mem_eigenspace_iff, mem_eigSp, hL, Matrix.toLin'_apply]
    refine ⟨fun h => h α, fun h c' => ?_⟩
    obtain ⟨N, p, hN, hp⟩ := hmul c'
    have hNC : (N : ℂ) ≠ 0 := Int.cast_ne_zero.2 hN
    have key : φ ((N : 𝓞 F) * c') *ᵥ u = τ (((N : 𝓞 F) * c' : 𝓞 F) : F) • u := by
      rw [hp, ← Matrix.toLin'_apply, toLin'_map_aeval_int]
      by_cases hu : u = 0
      · simp [hu]
      have hev : L.HasEigenvector (τ ((α : 𝓞 F) : F)) u :=
        ⟨Module.End.mem_eigenspace_iff.2 (by rw [hL, Matrix.toLin'_apply]; exact h), hu⟩
      rw [← hL, Module.End.aeval_apply_of_hasEigenvector hev]
      congr 1
      have h2 : (τ.comp (algebraMap (𝓞 F) F)) (aeval α p) = aeval ((τ.comp (algebraMap (𝓞 F) F)) α) p :=
        (Polynomial.aeval_algHom_apply (τ.comp (algebraMap (𝓞 F) F)).toIntAlgHom α p).symm
      simp only [RingHom.comp_apply] at h2
      rw [RingOfIntegers.coe_eq_algebraMap, h2, Polynomial.eval_map_algebraMap]
    have e1 : φ ((N : 𝓞 F) * c') = (N : ℂ) • φ c' := by
      rw [map_mul, map_intCast, Int.cast_smul_eq_zsmul, zsmul_eq_mul]
    have e2 : τ (((N : 𝓞 F) * c' : 𝓞 F) : F) = (N : ℂ) * τ (c' : F) := by
      simp
    rw [e1, e2, Matrix.smul_mulVec, mul_smul] at key
    exact smul_right_injective _ hNC key

  have hind : iSupIndep (eigSp φ) := by
    have := iSupIndep.comp (Module.End.eigenspaces_iSupIndep L) hinj
    convert this using 1
    funext τ
    exact hW τ
  have htop : ⨆ τ, eigSp φ τ = ⊤ := by
    rw [eq_top_iff, ← hss.iSup_eigenspace_eq_top, iSup_le_iff]
    intro m
    by_cases hm : L.eigenspace m = ⊥
    · rw [hm]; exact bot_le
    · obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
      have hev : L.HasEigenvector m u := ⟨hu, hu0⟩
      have h0 := Module.End.aeval_apply_of_hasEigenvector hev
        (p := ∏ τ : F →+* ℂ, (X - C (τ ((α : 𝓞 F) : F))))
      rw [hLf, LinearMap.zero_apply, eq_comm, smul_eq_zero] at h0
      have hroot := h0.resolve_right hu0
      rw [eval_prod, Finset.prod_eq_zero_iff] at hroot
      obtain ⟨τ, -, hτ⟩ := hroot
      rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hτ
      rw [hτ, ← hW τ]
      exact le_iSup (eigSp φ) τ
  have hint : DirectSum.IsInternal (eigSp φ) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  have hmaps : ∀ τ, Set.MapsTo (Matrix.toLin' (φ c)) (eigSp φ τ) (eigSp φ τ) := by
    intro τ u hu
    have hu' := (mem_eigSp φ τ u).1 hu
    show Matrix.toLin' (φ c) u ∈ eigSp φ τ
    rw [Matrix.toLin'_apply, hu' c]
    exact (eigSp φ τ).smul_mem _ hu
  rw [← Matrix.trace_toLin'_eq, LinearMap.trace_eq_sum_trace_restrict hint hmaps]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hres : (Matrix.toLin' (φ c)).restrict (hmaps τ) = τ (c : F) • LinearMap.id := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    have hv := (mem_eigSp φ τ v).1 v.2
    show Matrix.toLin' (φ c) (v : Fin g → ℂ) = τ (c : F) • (v : Fin g → ℂ)
    rw [Matrix.toLin'_apply, hv c]
  rw [hres, map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]

end GlobalTheory.UPel.HT.LieType
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ChernSpec

open GlobalTheory.EtC.ClsSpec

set_option backward.isDefEq.respectTransparency false

theorem sec_neg {R : Type} [CommRing R] (F : Shv R) (s : ℤ) (hs : s < 0) {U : Scheme.{0}}
    (a b : Sec ((res R F).X s) U) : a = b := by
  have hZ : IsZero ((res R F).X s) :=
    CochainComplex.isZero_of_isStrictlyGE ((injectiveResolution F).cochainComplex) 0 s hs
  have h := hZ.eq_of_src (𝟙 _) 0
  have ha : Sec.map (𝟙 _) a = Sec.map (0 : (res R F).X s ⟶ _) a := by rw [h]
  have hb : Sec.map (𝟙 _) b = Sec.map (0 : (res R F).X s ⟶ _) b := by rw [h]
  simp [Sec.map] at ha hb
  rw [ha, hb]

theorem lineUnit_face_res {E : Spc} (L : E ⟶ ofCat (glCat 1)) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E 2 U) (i : Fin 3) :
    lineUnit L ((x.res g).face i) = umap g (lineUnit L (x.face i)) := by
  rw [← face_res, ClsSpec.lineUnit_res]

theorem rep_unique (q : ℕ) [NeZero q] {E : Spc} (hE : Inv q E) (L : E ⟶ ofCat (glCat 1))
    (γ γ' : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2)
    (h0 : ∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ 0 2 (by simp) U x = 0)
    (h1 : ∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev γ 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v))
    (h2 : ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.face 2) →
      w ^ q = lineUnit L (x.face 0) → ev γ 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w))
    (h0' : ∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ' 0 2 (by simp) U x = 0)
    (h1' : ∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev γ' 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v))
    (h2' : ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.face 2) →
      w ^ q = lineUnit L (x.face 0) → ev γ' 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)) :
    γ = γ' := by
  refine (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 _ _ fun p s hs U x => ?_
  match p with
  | 0 =>
    obtain rfl : s = 2 := by omega
    rw [h0, h0']
  | 1 =>
    obtain rfl : s = 1 := by omega
    refine ClsSpec.sep (ClsSpec.loc_mono (root_loc (hE U ⟨x.face 0⟩) (lineUnit L x)) fun V g ⟨v, hv⟩ => ?_)
    have hv' : v ^ q = lineUnit L (x.res g) := by rw [ClsSpec.lineUnit_res]; exact hv
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ 1 1 _ V U g x, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ' 1 1 _ V U g x,
      h1 V _ v hv', h1' V _ v hv']
  | 2 =>
    obtain rfl : s = 0 := by omega
    have hU := hE U ⟨(x.face 0).face 0⟩
    refine ClsSpec.sep (ClsSpec.loc_mono (ClsSpec.loc_and (root_loc hU (lineUnit L (x.face 2))) (root_loc hU (lineUnit L (x.face 0))))
      fun V g ⟨⟨v, hv⟩, w, hw⟩ => ?_)
    rw [← lineUnit_face_res] at hv hw
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ 2 0 _ V U g x, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ' 2 0 _ V U g x,
      h2 V _ v w hv hw, h2' V _ v w hv hw]
  | p + 3 => exact sec_neg _ _ (by omega) _ _

theorem rep_comp (q : ℕ) {E E' : Spc} (f : E ⟶ E') (L : E' ⟶ ofCat (glCat 1))
    (γ : Cochain ((chains (ZMod q)).obj E') (res _ (tw q 1)) 2)
    (h0 : ∀ (U : Scheme.{0}) (x : Sx E' 0 U), ev γ 0 2 (by simp) U x = 0)
    (h1 : ∀ (U : Scheme.{0}) (x : Sx E' 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev γ 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v))
    (h2 : ∀ (U : Scheme.{0}) (x : Sx E' 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.face 2) →
      w ^ q = lineUnit L (x.face 0) → ev γ 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)) :
    (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev ((Cochain.ofHom ((chains (ZMod q)).map f)).comp γ (zero_add 2)) 0 2 (by simp) U x = 0) ∧
    (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit (f ≫ L) x →
      ev ((Cochain.ofHom ((chains (ZMod q)).map f)).comp γ (zero_add 2)) 1 1 (by simp) U x =
        Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧
    (∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit (f ≫ L) (x.face 2) →
      w ^ q = lineUnit (f ≫ L) (x.face 0) →
      ev ((Cochain.ofHom ((chains (ZMod q)).map f)).comp γ (zero_add 2)) 2 0 (by simp) U x =
        kumT q U v + kumT q U w - kumT q U (v * w)) := by
  refine ⟨fun U x => ?_, fun U x v hv => ?_, fun U x v w hv hw => ?_⟩
  · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.1 f γ]; exact h0 U _
  · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.1 f γ]; exact h1 U _ v hv
  · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.1 f γ]
    refine h2 U _ v w ?_ ?_
    · rw [← map_face]; exact hv
    · rw [← map_face]; exact hw

theorem face_forms (q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (γ : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2)
    (h2 : ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      w ^ q = lineUnit L (x.sub 1 1 (by omega)) → ev γ 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)) :
    ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.face 2) →
      w ^ q = lineUnit L (x.face 0) → ev γ 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w) :=
  fun U x v w hv hw => h2 U x v w (by rw [sub_zero_one]; exact hv) (by rw [sub_one_one]; exact hw)

theorem firstChernClassTateTwist_pullback (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') (L : E' ⟶ ofCat (glCat 1)) (hE' : Inv q E') :
    pull _ f _ _ (c1 q L) = c1 q (f ≫ L) := by
  have hE : Inv q E := fun U ⟨x⟩ => hE' U ⟨x.map f⟩
  obtain ⟨γ, hγ, h0, h1, h2⟩ := firstChernClassTateTwist_cocycle_representative q hE' L
  obtain ⟨γ', hγ', h0', h1', h2'⟩ := firstChernClassTateTwist_cocycle_representative q hE (f ≫ L)
  obtain ⟨k0, k1, k2⟩ := rep_comp q f L γ.1 h0 h1 (face_forms q L γ.1 h2)
  have key := rep_unique q hE (f ≫ L) _ γ'.1 k0 k1 k2 h0' h1' (face_forms q (f ≫ L) γ'.1 h2')
  rw [← hγ, ← hγ']
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map f)) γ (zero_add 2)) = _
  congr 1
  exact Cocycle.ext key

end GlobalTheory.EtC.ChernSpec

namespace GlobalTheory.EtC.ChernSpec
open GlobalTheory.EtC.ClsSpec
set_option backward.isDefEq.respectTransparency false

theorem isOneCochain_add (q : ℕ) [NeZero q] {E : Spc} (L M N : E ⟶ ofCat (glCat 1)) (hE : Inv q E)
    (hN : ∀ (U : Scheme.{0}) (x : Sx E 1 U), lineUnit N x = lineUnit L x * lineUnit M x) :
    c1 q N = c1 q L + c1 q M := by
  obtain ⟨γL, hL, l0, l1, l2⟩ := firstChernClassTateTwist_cocycle_representative q hE L
  obtain ⟨γM, hM, m0, m1, m2⟩ := firstChernClassTateTwist_cocycle_representative q hE M
  obtain ⟨γN, hN', n0, n1, n2⟩ := firstChernClassTateTwist_cocycle_representative q hE N
  have l2' := face_forms q L γL.1 l2
  have m2' := face_forms q M γM.1 m2
  have n2' := face_forms q N γN.1 n2
  have hq₁ : ∀ (U : Scheme.{0}) (_ : Sx E 1 U), IsUnit (q : Γ(U, ⊤)) := fun U x => hE U ⟨x.face 0⟩
  obtain ⟨b, hb, hbv⟩ : ∃ b : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res _ (tw q 1)).X 0) U,
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 1 U), Sec.res g (b U x) = b V (x.res g)) ∧
      ∀ (U : Scheme.{0}) (x : Sx E 1 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x → w ^ q = lineUnit M x →
        b U x = kumT q U v + kumT q U w - kumT q U (v * w) := by
    rcases kumT_cases q with ht | ht
    · exact exists_two_family ht hq₁ (fun U x => lineUnit L x) (fun U x => lineUnit M x)
        (fun V U g x => ClsSpec.lineUnit_res L g x) (fun V U g x => ClsSpec.lineUnit_res M g x)
    · refine ⟨fun _ _ => 0, fun V U g x => map_zero _, fun U x v w _ _ => ?_⟩
      rw [ht]
      simp
  obtain ⟨β, hβ1, hβ0⟩ := exists_single (R := ZMod q) (E := E) (I := res _ (tw q 1)) (n := 1) 1 0 (by simp) b hb
  rw [← hL, ← hM, ← hN', eq_comm, ← sub_eq_zero, ← CohomologyClass.mk_add, ← CohomologyClass.mk_sub,
    CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ 1 (by norm_num)]
  refine ⟨β, ?_⟩
  apply (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1
  intro p t ht U x
  rw [Cocycle.coe_sub, Cocycle.coe_add, ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).1 _ _ p t ht U x).2.1,
    ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).1 _ _ p t ht U x).1]
  match p with
  | 0 =>
    obtain rfl : t = 2 := by omega
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (by norm_num) β U).1 x, hβ0 _ _ _ _ _ (by decide), smap_zero, l0, m0, n0]
    simp
  | 1 =>
    obtain rfl : t = 1 := by omega
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (by norm_num) β U).2 0 0 1 (by simp) ht x]
    rw [Finset.sum_eq_zero fun i _ => by rw [hβ0 _ _ _ _ _ (by decide), smul_zero], smul_zero, add_zero, hβ1]
    refine ClsSpec.sep (ClsSpec.loc_mono (ClsSpec.loc_and (root_loc (hq₁ U x) (lineUnit L x))
      (root_loc (hq₁ U x) (lineUnit M x))) fun V g ⟨⟨v, hv⟩, w, hw⟩ => ?_)
    rw [← ClsSpec.lineUnit_res] at hv hw
    rw [res_map, hb, hbv V _ v w hv hw, res_sub, res_add,
      (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γL.1 1 1 _ V U g x, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γM.1 1 1 _ V U g x,
      (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γN.1 1 1 _ V U g x, l1 V _ v hv, m1 V _ w hw,
      n1 V _ (v * w) (by rw [mul_pow, hv, hw, hN]), smap_sub, smap_add]
  | 2 =>
    obtain rfl : t = 0 := by omega
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (by norm_num) β U).2 1 (-1) 0 (by simp) ht x]
    rw [hβ0 _ _ _ _ _ (by decide), smap_zero, zero_add, Fin.sum_univ_three, hβ1, hβ1, hβ1]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_smul, neg_smul, Int.reduceNeg]
    rw [Int.negOnePow_even 2 (by decide), one_smul, ← sub_eq_add_neg]
    have hU := hE U ⟨(x.face 0).face 0⟩
    refine ClsSpec.sep (ClsSpec.loc_mono (ClsSpec.loc_and
      (ClsSpec.loc_and (root_loc hU (lineUnit L (x.face 2))) (root_loc hU (lineUnit L (x.face 0))))
      (ClsSpec.loc_and (root_loc hU (lineUnit M (x.face 2))) (root_loc hU (lineUnit M (x.face 0)))))
      fun V g ⟨⟨⟨a, ha⟩, c, hc⟩, ⟨a', ha'⟩, c', hc'⟩ => ?_)
    rw [← lineUnit_face_res] at ha hc ha' hc'
    have hN2 : ∀ i, lineUnit N ((x.res g).face i) = lineUnit L ((x.res g).face i) * lineUnit M ((x.res g).face i) :=
      fun i => hN V _
    simp only [res_add, res_sub, neg_one_sq, one_smul]
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γL.1 2 0 _ V U g x, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γM.1 2 0 _ V U g x,
      (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γN.1 2 0 _ V U g x, l2' V _ a c ha hc, m2' V _ a' c' ha' hc',
      n2' V _ (a * a') (c * c') (by rw [mul_pow, ha, ha', hN2]) (by rw [mul_pow, hc, hc', hN2])]
    rw [hb, hb, hb, face_res, face_res, face_res,
      hbv V _ c c' (by rw [hc]) (by rw [hc']),
      hbv V _ (a * c) (a' * c') (by rw [lineUnit_face, mul_pow, ha, hc]) (by rw [lineUnit_face, mul_pow, ha', hc']),
      hbv V _ a a' ha ha']
    have e : a * c * (a' * c') = a * a' * (c * c') := by rw [mul_mul_mul_comm]
    rw [e]
    abel
  | p + 3 => exact sec_neg _ _ (by omega) _ _

end GlobalTheory.EtC.ChernSpec

theorem _root_.GlobalTheory.EtC.firstChernClassTateTwist_cocycle_naturality_additivity : ∀ (q : ℕ) [NeZero q], (∀ {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E → ∃ γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, CohomologyClass.mk γ = c1 q L ∧ (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 2 (by simp) U x = 0) ∧ (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x → ev γ.1 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧ ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) → w ^ q = lineUnit L (x.sub 1 1 (by omega)) → ev γ.1 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)) ∧ (∀ {E E' : Spc} (f : E ⟶ E') (L : E' ⟶ ofCat (glCat 1)), Inv q E' → pull _ f _ _ (c1 q L) = c1 q (f ≫ L)) ∧ ∀ {E : Spc} (L M N : E ⟶ ofCat (glCat 1)), Inv q E → (∀ (U : Scheme.{0}) (x : Sx E 1 U), lineUnit N x = lineUnit L x * lineUnit M x) → c1 q N = c1 q L + c1 q M := by
  intro q _
  exact ⟨fun L hE => firstChernClassTateTwist_cocycle_representative q hE L, fun f L hE' => GlobalTheory.EtC.ChernSpec.firstChernClassTateTwist_pullback q f L hE',
    fun L M N hE hN => GlobalTheory.EtC.ChernSpec.isOneCochain_add q L M N hE hN⟩

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

theorem _root_.GlobalTheory.T.clopenCond_injective_geom_alt : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (K : Over S) (κ : K ⟶ o.A), IsFinite K.hom → Etale K.hom → (∀ c ∈ w0 ^ r, κ ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ K, y ≫ κ = x) → ∀ (Z : Over S) (et : D.La → (Z ⟶ o.A)), IsFinite Z.hom → Etale Z.hom → (∀ x y, et (x + y) = et x * et y) → (∀ (c : D.O) x, et (c • x) = et x ≫ o.act.act c) → (∀ x ∈ wSub D w0 r, et x = 1) → GlobalTheory.LevCover.ClopenCond Z fun T' h => ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T'.left), (∀ y, (Over.homMk x rfl : Over.mk (x ≫ T'.hom) ⟶ T') ≫ h ≫ et y = 1 → y ∈ wSub D w0 r) := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.clopenCond_injective_geom) | (exact GlobalTheory.UPel.HT.EtLev.clopenCond_injective_geom) | (intros; apply GlobalTheory.UPel.HT.EtLev.clopenCond_injective_geom <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

theorem _root_.GlobalTheory.T.clopenCond_onto_alt : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (K : Over S) (κ : K ⟶ o.A), IsFinite K.hom → Etale K.hom → (∀ c ∈ w0 ^ r, κ ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ K, y ≫ κ = x) → ∀ (Z : Over S) (et : D.La → (Z ⟶ o.A)), IsFinite Z.hom → Etale Z.hom → (∀ x y, et (x + y) = et x * et y) → (∀ (c : D.O) x, et (c • x) = et x ≫ o.act.act c) → (∀ x ∈ wSub D w0 r, et x = 1) → GlobalTheory.LevCover.ClopenCond Z fun T' h => ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T'.left), ∀ g : Over.mk (x ≫ T'.hom) ⟶ o.A, (∀ c ∈ w0 ^ r, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃ y, (Over.homMk x rfl : Over.mk (x ≫ T'.hom) ⟶ T') ≫ h ≫ et y = g := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.clopenCond_onto) | (exact GlobalTheory.UPel.HT.EtLev.clopenCond_onto) | (intros; apply GlobalTheory.UPel.HT.EtLev.clopenCond_onto <;> assumption)
end

section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

theorem _root_.GlobalTheory.T.exists_conj_inv_section_mul_entries_near_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (σ : V (nd X) → realSU X.Ψ X.Gm), IsOrth X x → σ 0 = 1 → ContinuousAt σ 0 → ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ z : V (nd X), ‖z‖ < κ → ∀ g ∈ grpBall (realSU X.Ψ X.Gm) ε, ∀ τ a b, ‖((mat x τ)⁻¹ * (((((σ z)⁻¹ * g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ) a b - (1 : Matrix (Fin r) (Fin r) ℂ) a b‖ < η := by
  first | exact @GlobalTheory.SUVol.conj_inv_section_mul_entries_near_one | exact GlobalTheory.SUVol.conj_inv_section_mul_entries_near_one | (intros; apply GlobalTheory.SUVol.conj_inv_section_mul_entries_near_one <;> assumption)
end

section

open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

theorem _root_.GlobalTheory.T.offDiagBlockNorm_mul_invariant : ∀ (n : ℕ) (ε : Fin n → Bool), (Continuous fun g : UJ ε => ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2) ∧ ∀ (k k' : KG ε) (g : UJ ε), ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM ((k : UJ ε) * g * (k' : UJ ε))) z.1.1 z.1.2‖ ^ 2 = ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2 := by
  first | exact @GlobalTheory.offDiagBlockNorm_cont_inv | exact GlobalTheory.offDiagBlockNorm_cont_inv | (intros; apply GlobalTheory.offDiagBlockNorm_cont_inv <;> assumption)
end
